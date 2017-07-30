use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::iter::Peekable;
use std::str::Chars;

//
// Public grammar types
//

pub type Terminal        = char;
pub type NonTerminal<'a> = &'a str;

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum RuleElement<'a> {
    Empty,
    Terminal(char),
    NonTerminal(&'a str),
}

pub type Rule<'a>    = Vec<RuleElement<'a>>;
pub type Grammar<'a> = BTreeMap<NonTerminal<'a>, Vec<Rule<'a>>>;

#[derive(Clone, Debug, PartialEq)]
pub enum GrammarError<'a> {
    NoStartSymbol,
    EmptyGrammar,
    InvalidGrammar {
        non_terminal: NonTerminal<'a>,
        rule:         Rule<'a>,
        rule_element: RuleElement<'a>,
    },
    Conflict {
        non_terminal: NonTerminal<'a>,
        rule:         Rule<'a>,
        rule_element: RuleElement<'a>,
    },
}

//
// Public parsing types
//

#[derive(Clone, Debug, PartialEq)]
pub enum ParseTree<'a> {
    Terminal(char),
    NonTerminal {
        symbol:   &'a str,
        children: Vec<ParseTree<'a>>,
    },
}

#[derive(Clone, Debug, PartialEq)]
pub enum ParseError {
    NoMoreInput,
    InvalidInput(u64),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Parser<'a> {
    parse_table: ParseTable<'a>,
}

//
// Public functions
//

impl <'a>Parser<'a> {
    pub fn new(grammar: &'a Grammar) -> Result<Parser<'a>, GrammarError<'a>> {
        match grammar.contains_key("START") {
            false => Err(GrammarError::NoStartSymbol),
            true  => match grammar.len() > 1 {
                false => Err(GrammarError::EmptyGrammar),
                true  => {
                    let first_set = match get_first_set(&grammar) {
                        Ok(first_set) => first_set,
                        Err(err)      => return Err(err),
                    };

                    let follow_set = get_follow_set(&grammar, &first_set);

                    match get_parse_table(&grammar, &first_set, &follow_set) {
                        Ok(parse_table) => Ok(Parser { parse_table: parse_table }),
                        Err(err)        => Err(err),
                    }
                },
            },
        }
    }

    pub fn parse(&mut self, input: &'a str) -> Result<ParseTree<'a>, ParseError> {
        let mut parse_tree = ParseTree::NonTerminal {
            symbol:   "START",
            children: vec![],
        };

        let mut input_stack = InputStack {
            input: input.chars().peekable(),
            index: 0,
        };

        match self._parse(&mut parse_tree, &mut input_stack) {
            Some(err) => Err(err),
            None      => match input_stack.input.peek().is_some() {
                true  => Err(ParseError::InvalidInput(input_stack.index)),
                false => Ok(parse_tree),
            },
        }
    }

    fn _parse(&self, parse_tree: &mut ParseTree<'a>, input_stack: &mut InputStack<'a>) -> Option<ParseError> {
        //  if current node is non-terminal
        //      get parse table entry
        //
        //      foreach rule element from parse table entry
        //          if rule element is a terminal
        //              add consumed input as a child node
        //          else
        //              add non-terminal rule element as a child node
        //              recurse

        match *parse_tree {
            ParseTree::Terminal(_)                              => { panic!("This should never happen") },
            ParseTree::NonTerminal { symbol, ref mut children } => {
                let parse_table_entry = match input_stack.input.peek() {
                    None             => return Some(ParseError::NoMoreInput),
                    Some(next_input) => match self.parse_table.get(symbol).unwrap().get(&next_input) {
                        None       => return Some(ParseError::InvalidInput(input_stack.index)),
                        Some(rule) => rule,
                    },
                };

                for rule_element in parse_table_entry {
                    match *rule_element {
                        RuleElement::Empty       => {},
                        RuleElement::Terminal(u) => {
                            match input_stack.input.next() {
                                None             => return Some(ParseError::NoMoreInput),
                                Some(next_input) => {
                                    match u == next_input {
                                        false => return Some(ParseError::InvalidInput(input_stack.index)),
                                        true  => children.push(ParseTree::Terminal(next_input)),
                                    }

                                    input_stack.index = input_stack.index + 1;
                                },
                            }
                        },
                        RuleElement::NonTerminal(u) => {
                            let mut child = ParseTree::NonTerminal {
                                symbol:   u,
                                children: vec![],
                            };

                            match self._parse(&mut child, input_stack) {
                                None        => children.push(child),
                                Some(error) => return Some(error),
                            }
                        },
                    }
                }
            },
        }

        None
    }
}

//
// Private parsing types
//

type ParseTable<'a> = BTreeMap<NonTerminal<'a>, BTreeMap<Terminal, Rule<'a>>>;

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum FirstElement {
    Empty,
    Terminal(char),
}

type FirstSet<'a>   = BTreeMap<NonTerminal<'a>, BTreeSet<FirstElement>>;
type FollowSet<'a>  = BTreeMap<NonTerminal<'a>, BTreeSet<Terminal>>;

struct InputStack<'a> {
    input: Peekable<Chars<'a>>,
    index: u64,
}

//
// Private functions
//

fn get_first_set<'a>(grammar: &Grammar<'a>) -> Result<FirstSet<'a>, GrammarError<'a>> {
    //  while no change
    //      foreach rule A -> RHS
    //          if RHS == {Empty}
    //              FirstSet(A) += Empty
    //              continue
    //
    //          while FirstSet(Ui) derives Empty
    //              Replace Ui with U(i+1)
    //              break to next rule if no more Ui
    //
    //          if Ui is a terminal
    //              FirstSet(A) += terminal
    //              break to next rule
    //
    //          FirstSet(A) += FirstSet(Ui)

    let mut first_set: FirstSet
        = grammar
            .keys()
            .map(|&non_terminal| (non_terminal, BTreeSet::new()))
            .collect();

    loop {
        let mut has_changed = false;

        for (non_terminal, rules) in grammar {
            if rules.is_empty() {
                return Err(GrammarError::InvalidGrammar {
                    non_terminal: non_terminal,
                    rule:         vec![],
                    rule_element: RuleElement::Empty,
                });
            }
            
            for rule in rules {
                let mut has_empty = false;

                for rule_element in rule {
                    match *rule_element {
                        RuleElement::Empty       => { has_empty = true },
                        RuleElement::Terminal(u) => {
                            if first_set.get_mut(non_terminal).unwrap().insert(FirstElement::Terminal(u)) {
                                has_changed = true;
                            }

                            break;
                        },
                        RuleElement::NonTerminal(u) => {
                            match u == *non_terminal {
                                true  => continue,
                                false => {
                                    let mut first_rule_element_clone = match first_set.get(u) {
                                        Some(first_rule_element) => first_rule_element.clone(),
                                        None                     => return Err(GrammarError::InvalidGrammar {
                                            non_terminal: non_terminal,
                                            rule:         rule.clone(),
                                            rule_element: rule_element.clone(),
                                        }),
                                    };

                                    let mut first_non_terminal = first_set.get_mut(non_terminal).unwrap();
                                    let old_length             = first_non_terminal.len();

                                    let has_empty = first_rule_element_clone.remove(&FirstElement::Empty);
                                    first_non_terminal.extend(first_rule_element_clone);

                                    if old_length != first_non_terminal.len() {
                                        has_changed = true;
                                    }

                                    match has_empty {
                                        true  => continue,
                                        false => break,
                                    }
                                },
                            }
                        },
                    }
                }

                match has_empty && (1 == rule.iter().len()) {
                    false => continue,
                    true  => {
                        let mut first_non_terminal = first_set.get_mut(non_terminal).unwrap();

                        match first_non_terminal.contains(&FirstElement::Empty) {
                            true  => continue,
                            false => {
                               first_non_terminal.insert(FirstElement::Empty);
                               has_changed = true;
                            },
                        }
                    },
                }
            }
        }

        match has_changed {
            true  => continue,
            false => break,
        }
    }

    Ok(first_set)
}

fn get_follow_set<'a>(grammar: &Grammar<'a>, first_set: &FirstSet<'a>) -> FollowSet<'a> {
    //  while no change
    //      foreach rule where we have A => ...By...
    //          FollowSet(B) += FirstSet(y)
    //
    //          if y derives or *is* Empty
    //              FollowSet(B) += FollowSet(A)

    let mut follow_set: FollowSet
        = grammar
            .keys()
            .map(|&non_terminal| (non_terminal, BTreeSet::new()))
            .collect();

    loop {
        let mut has_changed = false;

        for (non_terminal, rules) in grammar {
            let follow_non_terminal = follow_set.get(non_terminal).unwrap().clone();

            for rule in rules {
                for (i, rule_element_b) in rule.iter().enumerate() {
                    match *rule_element_b {
                        RuleElement::Empty          => {},
                        RuleElement::Terminal(_)    => {},
                        RuleElement::NonTerminal(b) => {
                            let mut follow_rule_element_b = follow_set.get_mut(&b).unwrap();
                            let mut extend_from_empty     = false;

                            for rule_element_y in rule.iter().skip(i + 1) {
                                match *rule_element_y {
                                    RuleElement::Empty       => {},
                                    RuleElement::Terminal(y) => {
                                        if follow_rule_element_b.insert(y) {
                                            has_changed = true;
                                        }

                                        break;
                                    },
                                    RuleElement::NonTerminal(y) => {
                                        let mut first_rule_element_y = first_set.get(y).unwrap().clone();

                                        let has_empty
                                            =  first_rule_element_y.remove(&FirstElement::Empty)
                                            || first_rule_element_y.len() == 0;

                                        for first_y in first_rule_element_y {
                                            match first_y {
                                                FirstElement::Empty        => {},
                                                FirstElement::Terminal(fy) => {
                                                    match follow_rule_element_b.insert(fy) {
                                                        true  => has_changed = true,
                                                        false => continue,
                                                    }
                                                },
                                            }
                                        }

                                        match has_empty {
                                            true  => extend_from_empty = true,
                                            false => break,
                                        }
                                    },
                                }
                            }

                            match extend_from_empty || (i + 1) == rule.iter().len() {
                                true  => follow_rule_element_b.extend(follow_non_terminal.clone()),
                                false => continue,
                            }
                        },
                    }
                }
            }
        }

        match has_changed {
            true  => continue,
            false => break,
        }
    }

    follow_set
}

fn get_parse_table<'a>(
        grammar:    &Grammar<'a>,
        first_set:  &FirstSet<'a>,
        follow_set: &FollowSet<'a>
    ) -> Result<ParseTable<'a>, GrammarError<'a>> {
    //  foreach rule A -> RHS
    //      foreach terminal a in FirstSet(RHS)
    //          [A, a] = RHS
    //
    //      if RHS is, or derives, Empty
    //          foreach terminal a in FollowSet(A)
    //              [A, a] = RHS

    let mut parse_table: ParseTable
        = grammar
            .keys()
            .map(|&non_terminal| (non_terminal, BTreeMap::new()))
            .collect();

    for (non_terminal, rules) in grammar {
        let parse_table_non_terminal = parse_table.get_mut(non_terminal).unwrap();
        let follow_non_terminal      = follow_set.get(non_terminal).unwrap();

        for rule in rules {
            let mut extend_from_empty = false;

            for rule_element in rule {
                match *rule_element {
                    RuleElement::Empty       => { extend_from_empty = true },
                    RuleElement::Terminal(u) => {
                        match parse_table_non_terminal.insert(u, rule.clone()).is_some() {
                            false => break,
                            true  => return Err(GrammarError::Conflict {
                                non_terminal: non_terminal,
                                rule:         rule.clone(),
                                rule_element: rule_element.clone(),
                            }),
                        }
                    }
                    RuleElement::NonTerminal(u) => {
                        let mut first_rule_element = first_set.get(u).unwrap().clone();
                        let has_empty              = first_rule_element.remove(&FirstElement::Empty);

                        for first_u in first_rule_element {
                            match first_u {
                                FirstElement::Empty        => {},
                                FirstElement::Terminal(fu) => {
                                    match parse_table_non_terminal.insert(fu, rule.clone()).is_some() {
                                        false => continue,
                                        true  => return Err(GrammarError::Conflict {
                                            non_terminal: non_terminal,
                                            rule:         rule.clone(),
                                            rule_element: rule_element.clone(),
                                        }),
                                    }
                                },
                            }
                        }

                        match has_empty {
                            true  => continue,
                            false => break,
                        }
                    },
                }
            }

            match extend_from_empty {
                false => continue,
                true  => {
                    for follow_u in follow_non_terminal {
                        match parse_table_non_terminal.insert(*follow_u, rule.clone()).is_some() {
                            false => continue,
                            true  => return Err(GrammarError::Conflict {
                                non_terminal: non_terminal,
                                rule:         rule.clone(),
                                rule_element: RuleElement::Empty,
                            }),
                        }
                    }
                },
            }
        }
    }

    Ok(parse_table)
}

//  TODO:
//      - Now that the tests show the parser works, generate the tests using the parser itself
//        e.g "A = [[ET(a)N(B)]]"

#[cfg(test)]
mod new {
    use super::*;

    #[test]
    fn no_start_symbol() {
        let grammar = Grammar::new();

        match Parser::new(&grammar) {
            Ok(_)    => panic!(),
            Err(err) => assert!(err == GrammarError::NoStartSymbol),
        }
    }

    #[test]
    fn empty_grammar() {
        let mut grammar = Grammar::new();
        grammar.insert("START", vec![]);

        match Parser::new(&grammar) {
            Err(err) => assert!(err == GrammarError::EmptyGrammar),
            Ok(_)    => panic!(),
        }
    }

    #[test]
    fn bad_parse_table() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Terminal('a'), RuleElement::Terminal('b')],
            vec![RuleElement::Terminal('a'), RuleElement::Terminal('c')],
        ]);

        match Parser::new(&grammar) {
            Ok(_)    => panic!(),
            Err(err) => assert!(err == GrammarError::Conflict {
                non_terminal: "A",
                rule:         vec![RuleElement::Terminal('a'), RuleElement::Terminal('c')],
                rule_element: RuleElement::Terminal('a'),
            }),
        }
    }

    #[test]
    fn ok() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Terminal('a'), RuleElement::Terminal('b')],
        ]);

        match Parser::new(&grammar) {
            Err(_)     => panic!(),
            Ok(parser) => {
                let mut start_rules = BTreeMap::new();
                start_rules.insert('a', vec![RuleElement::NonTerminal("A")]);

                let mut a_rules = BTreeMap::new();
                a_rules.insert('a', vec![RuleElement::Terminal('a'), RuleElement::Terminal('b')]);

                let mut expected_parse_table  = BTreeMap::new();
                expected_parse_table.insert("START", start_rules);
                expected_parse_table.insert("A",     a_rules);

                assert!(parser == Parser { parse_table: expected_parse_table });
            },
        }
    }
}

#[cfg(test)]
mod parse {
    use super::*;

    #[test]
    fn no_more_input() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Terminal('a'), RuleElement::Terminal('b')],
        ]);

        let mut parser = Parser::new(&grammar).unwrap();

        match parser.parse("") {
            Ok(_)    => panic!(),
            Err(err) => assert!(err == ParseError::NoMoreInput),
        }
    }

    #[test]
    fn invalid_input() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Terminal('a'), RuleElement::Terminal('b')],
        ]);

        let mut parser = Parser::new(&grammar).unwrap();

        match parser.parse("abb") {
            Ok(_)    => panic!(),
            Err(err) => assert!(err == ParseError::InvalidInput(2)),
        }
    }

    #[test]
    fn ok() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Terminal('a'), RuleElement::Terminal('b')],
        ]);

        let mut parser = Parser::new(&grammar).unwrap();

        match parser.parse("ab") {
            Err(_)         => panic!(),
            Ok(parse_tree) => assert!(parse_tree == ParseTree::NonTerminal {
                symbol:   "START",
                children: vec![
                    ParseTree::NonTerminal {
                        symbol:   "A",
                        children: vec![
                            ParseTree::Terminal('a'),
                            ParseTree::Terminal('b'),
                        ],
                    },
                ],
            }),
        }
    }
}

#[cfg(test)]
mod _parse {
    use super::*;

    #[test]
    #[should_panic]
    fn panic_on_terminal() {
        // in reality, this should never happen as we only ever enter _parse() on non-terminals

        let mut start_rules = BTreeMap::new();
        start_rules.insert('a', vec![RuleElement::Terminal('b')]);

        let mut parse_table  = BTreeMap::new();
        parse_table.insert("START", start_rules);

        let parser = Parser {
            parse_table: parse_table,
        };

        let mut parse_tree  = ParseTree::Terminal('a');
        let mut input_stack = InputStack {
            input: "a".chars().peekable(),
            index: 0,
        };

        match parser._parse(&mut parse_tree, &mut input_stack) {
           _  => {},
        }
    }

    #[test]
    fn no_input() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Terminal('a'), RuleElement::Terminal('b')],
        ]);

        let mut parser = Parser::new(&grammar).unwrap();

        match parser.parse("") {
            Ok(_)    => panic!(),
            Err(err) => assert!(err == ParseError::NoMoreInput ),
        }
    }

    #[test]
    fn invalid_input() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Terminal('a'), RuleElement::Terminal('b')],
        ]);

        let mut parser = Parser::new(&grammar).unwrap();

        match parser.parse("c") {
            Ok(_)    => panic!(),
            Err(err) => assert!(err == ParseError::InvalidInput(0)),
        }
    }

    #[test]
    fn no_more_input() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Terminal('a'), RuleElement::Terminal('b')],
        ]);

        let mut parser = Parser::new(&grammar).unwrap();

        match parser.parse("a") {
            Ok(_)    => panic!(),
            Err(err) => assert!(err == ParseError::NoMoreInput),
        }
    }

    #[test]
    fn invalid_wrong_terminal() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Terminal('a'), RuleElement::Terminal('b'), RuleElement::Terminal('c')],
        ]);

        let mut parser = Parser::new(&grammar).unwrap();

        match parser.parse("abd") {
            Ok(_)    => panic!(),
            Err(err) => assert!(err == ParseError::InvalidInput(2)),
        }
    }

    #[test]
    fn invalid_wrong_terminal_recursed() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Terminal('a'), RuleElement::NonTerminal("B"), RuleElement::Terminal('c')],
        ]);

        grammar.insert("B", vec![
            vec![RuleElement::Terminal('d'), RuleElement::Terminal('e')],
        ]);

        let mut parser = Parser::new(&grammar).unwrap();

        match parser.parse("adfc") {
            Ok(_)    => panic!(),
            Err(err) => assert!(err == ParseError::InvalidInput(2)),
        }
    }

    #[test]
    fn ok() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Terminal('a'), RuleElement::NonTerminal("B"), RuleElement::Terminal('c')],
        ]);

        grammar.insert("B", vec![
            vec![RuleElement::Terminal('d'), RuleElement::Terminal('e')],
        ]);

        let mut parser = Parser::new(&grammar).unwrap();

        match parser.parse("adec") {
            Err(_)         => panic!(),
            Ok(parse_tree) => assert!(parse_tree == ParseTree::NonTerminal {
                symbol:   "START",
                children: vec![
                    ParseTree::NonTerminal {
                        symbol:   "A",
                        children: vec![
                            ParseTree::Terminal('a'),
                            ParseTree::NonTerminal {
                                symbol:   "B",
                                children: vec![
                                    ParseTree::Terminal('d'),
                                    ParseTree::Terminal('e'),
                                ],
                            },
                            ParseTree::Terminal('c'),
                        ],
                    },
                ],
            }),
        }
    }
}

#[cfg(test)]
mod get_first_set {
    use super::*;

    #[test]
    fn is_empty() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![]);

        match get_first_set(&grammar) {
            Ok(_)    => panic!(),
            Err(err) => assert!(err == GrammarError::InvalidGrammar {
                non_terminal: "A",
                rule:         vec![],
                rule_element: RuleElement::Empty,
            }),
        }
    }

    #[test]
    fn matching_non_terminal() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        match get_first_set(&grammar) {
            Err(_)        => panic!(),
            Ok(first_set) => {
                let mut expected_first_set = BTreeMap::new();

                expected_first_set.insert("START", BTreeSet::new());
                expected_first_set.insert("A",     BTreeSet::new());

                assert!(first_set == expected_first_set);
            },
        }
    }

    #[test]
    fn invalid_grammar() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::NonTerminal("B")],
        ]);

        match get_first_set(&grammar) {
            Ok(_)    => panic!(),
            Err(err) => assert!(err == GrammarError::InvalidGrammar {
                non_terminal: "A",
                rule:         vec![RuleElement::NonTerminal("B")],
                rule_element: RuleElement::NonTerminal("B"),
            }),
        }
    }

    #[test]
    fn combo_e() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Empty],
        ]);

        match get_first_set(&grammar) {
            Err(_)        => panic!(),
            Ok(first_set) => {
                let mut expected_first_set: FirstSet = BTreeMap::new();

                let mut a_first = BTreeSet::new();
                a_first.insert(FirstElement::Empty);

                expected_first_set.insert("START", BTreeSet::new());
                expected_first_set.insert("A",     a_first);

                assert!(first_set == expected_first_set);
            },
        }
    }

    #[test]
    fn combo_t() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Terminal('a')],
        ]);

        match get_first_set(&grammar) {
            Err(_)        => panic!(),
            Ok(first_set) => {
                let mut expected_first_set = BTreeMap::new();

                let mut start_first = BTreeSet::new();
                start_first.insert(FirstElement::Terminal('a'));

                let mut a_first = BTreeSet::new();
                a_first.insert(FirstElement::Terminal('a'));

                expected_first_set.insert("START", start_first);
                expected_first_set.insert("A",     a_first);

                assert!(first_set == expected_first_set);
            },
        }
    }

    #[test]
    fn combo_et() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Empty, RuleElement::Terminal('b')],
        ]);

        match get_first_set(&grammar) {
            Err(_)        => panic!(),
            Ok(first_set) => {
                let mut expected_first_set = BTreeMap::new();

                let mut start_first = BTreeSet::new();
                start_first.insert(FirstElement::Terminal('b'));

                let mut a_first = BTreeSet::new();
                a_first.insert(FirstElement::Terminal('b'));

                expected_first_set.insert("START", start_first);
                expected_first_set.insert("A",     a_first);

                assert!(first_set == expected_first_set);
            },
        }
    }

    #[test]
    fn combo_ene() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Empty, RuleElement::NonTerminal("B")],
        ]);

        grammar.insert("B", vec![
            vec![RuleElement::Empty],
        ]);

        match get_first_set(&grammar) {
            Err(_)        => panic!(),
            Ok(first_set) => {
                let mut expected_first_set = BTreeMap::new();

                let mut b_first = BTreeSet::new();
                b_first.insert(FirstElement::Empty);

                expected_first_set.insert("START", BTreeSet::new());
                expected_first_set.insert("A",     BTreeSet::new());
                expected_first_set.insert("B",     b_first);

                assert!(first_set == expected_first_set);
            },
        }
    }

    #[test]
    fn combo_ent() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Empty, RuleElement::NonTerminal("B")],
        ]);

        grammar.insert("B", vec![
            vec![RuleElement::Terminal('c')],
        ]);

        match get_first_set(&grammar) {
            Err(_)        => panic!(),
            Ok(first_set) => {
                let mut expected_first_set = BTreeMap::new();

                let mut start_first = BTreeSet::new();
                start_first.insert(FirstElement::Terminal('c'));

                let mut a_first = BTreeSet::new();
                a_first.insert(FirstElement::Terminal('c'));

                let mut b_first = BTreeSet::new();
                b_first.insert(FirstElement::Terminal('c'));

                expected_first_set.insert("START", start_first);
                expected_first_set.insert("A",     a_first);
                expected_first_set.insert("B",     b_first);

                assert!(first_set == expected_first_set);
            },
        }
    }

    #[test]
    fn combo_te() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Terminal('a'), RuleElement::Empty],
        ]);

        match get_first_set(&grammar) {
            Err(_)        => panic!(),
            Ok(first_set) => {
                let mut expected_first_set = BTreeMap::new();

                let mut start_first = BTreeSet::new();
                start_first.insert(FirstElement::Terminal('a'));

                let mut a_first = BTreeSet::new();
                a_first.insert(FirstElement::Terminal('a'));

                expected_first_set.insert("START", start_first);
                expected_first_set.insert("A",     a_first);

                assert!(first_set == expected_first_set);
            },
        }
    }

    #[test]
    fn combo_tt() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Terminal('a'), RuleElement::Terminal('b')],
        ]);

        match get_first_set(&grammar) {
            Err(_)        => panic!(),
            Ok(first_set) => {
                let mut expected_first_set = BTreeMap::new();

                let mut start_first = BTreeSet::new();
                start_first.insert(FirstElement::Terminal('a'));

                let mut a_first = BTreeSet::new();
                a_first.insert(FirstElement::Terminal('a'));

                expected_first_set.insert("START", start_first);
                expected_first_set.insert("A",     a_first);

                assert!(first_set == expected_first_set);
            },
        }
    }

    #[test]
    fn combo_tn() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Terminal('a'), RuleElement::NonTerminal("B")],
        ]);

        grammar.insert("B", vec![
            vec![],
        ]);

        match get_first_set(&grammar) {
            Err(_)        => panic!(),
            Ok(first_set) => {
                let mut expected_first_set = BTreeMap::new();

                let mut start_first = BTreeSet::new();
                start_first.insert(FirstElement::Terminal('a'));

                let mut a_first = BTreeSet::new();
                a_first.insert(FirstElement::Terminal('a'));

                expected_first_set.insert("START", start_first);
                expected_first_set.insert("A",     a_first);
                expected_first_set.insert("B",     BTreeSet::new());

                assert!(first_set == expected_first_set);
            },
        }
    }

    #[test]
    fn combo_tne() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Terminal('a'), RuleElement::NonTerminal("B")],
        ]);

        grammar.insert("B", vec![
            vec![RuleElement::Empty],
        ]);

        match get_first_set(&grammar) {
            Err(_)        => panic!(),
            Ok(first_set) => {
                let mut expected_first_set = BTreeMap::new();

                let mut start_first = BTreeSet::new();
                start_first.insert(FirstElement::Terminal('a'));

                let mut a_first = BTreeSet::new();
                a_first.insert(FirstElement::Terminal('a'));

                let mut b_first = BTreeSet::new();
                b_first.insert(FirstElement::Empty);

                expected_first_set.insert("START", start_first);
                expected_first_set.insert("A",     a_first);
                expected_first_set.insert("B",     b_first);

                assert!(first_set == expected_first_set);
            },
        }
    }

    #[test]
    fn combo_tnt() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Terminal('a'), RuleElement::NonTerminal("B")],
        ]);

        grammar.insert("B", vec![
            vec![RuleElement::Terminal('c')],
        ]);

        match get_first_set(&grammar) {
            Err(_)        => panic!(),
            Ok(first_set) => {
                let mut expected_first_set = BTreeMap::new();

                let mut start_first = BTreeSet::new();
                start_first.insert(FirstElement::Terminal('a'));

                let mut a_first = BTreeSet::new();
                a_first.insert(FirstElement::Terminal('a'));

                let mut b_first = BTreeSet::new();
                b_first.insert(FirstElement::Terminal('c'));

                expected_first_set.insert("START", start_first);
                expected_first_set.insert("A",     a_first);
                expected_first_set.insert("B",     b_first);

                assert!(first_set == expected_first_set);
            },
        }
    }

    #[test]
    fn combo_ne_e() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::NonTerminal("B"), RuleElement::Empty],
        ]);

        grammar.insert("B", vec![
            vec![RuleElement::Empty],
        ]);

        match get_first_set(&grammar) {
            Err(_)        => panic!(),
            Ok(first_set) => {
                let mut expected_first_set = BTreeMap::new();

                let mut b_first = BTreeSet::new();
                b_first.insert(FirstElement::Empty);

                expected_first_set.insert("START", BTreeSet::new());
                expected_first_set.insert("A",     BTreeSet::new());
                expected_first_set.insert("B",     b_first);

                assert!(first_set == expected_first_set);
            },
        }
    }

    #[test]
    fn combo_nt_e() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::NonTerminal("B"), RuleElement::Empty],
        ]);

        grammar.insert("B", vec![
            vec![RuleElement::Terminal('c')],
        ]);

        match get_first_set(&grammar) {
            Err(_)        => panic!(),
            Ok(first_set) => {
                let mut expected_first_set = BTreeMap::new();

                let mut start_first = BTreeSet::new();
                start_first.insert(FirstElement::Terminal('c'));

                let mut a_first = BTreeSet::new();
                a_first.insert(FirstElement::Terminal('c'));

                let mut b_first = BTreeSet::new();
                b_first.insert(FirstElement::Terminal('c'));

                expected_first_set.insert("START", start_first);
                expected_first_set.insert("A",     a_first);
                expected_first_set.insert("B",     b_first);

                assert!(first_set == expected_first_set);
            },
        }
    }

    #[test]
    fn combo_ne_t() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::NonTerminal("B"), RuleElement::Terminal('c')],
        ]);

        grammar.insert("B", vec![
            vec![RuleElement::Empty],
        ]);

        match get_first_set(&grammar) {
            Err(_)        => panic!(),
            Ok(first_set) => {
                let mut expected_first_set = BTreeMap::new();

                let mut start_first = BTreeSet::new();
                start_first.insert(FirstElement::Terminal('c'));

                let mut a_first = BTreeSet::new();
                a_first.insert(FirstElement::Terminal('c'));

                let mut b_first = BTreeSet::new();
                b_first.insert(FirstElement::Empty);

                expected_first_set.insert("START", start_first);
                expected_first_set.insert("A",     a_first);
                expected_first_set.insert("B",     b_first);

                assert!(first_set == expected_first_set);
            },
        }
    }

    #[test]
    fn combo_nt_t() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::NonTerminal("B"), RuleElement::Terminal('c')],
        ]);

        grammar.insert("B", vec![
            vec![RuleElement::Terminal('d')],
        ]);

        match get_first_set(&grammar) {
            Err(_)        => panic!(),
            Ok(first_set) => {
                let mut expected_first_set = BTreeMap::new();

                let mut start_first = BTreeSet::new();
                start_first.insert(FirstElement::Terminal('d'));

                let mut a_first = BTreeSet::new();
                a_first.insert(FirstElement::Terminal('d'));

                let mut b_first = BTreeSet::new();
                b_first.insert(FirstElement::Terminal('d'));

                expected_first_set.insert("START", start_first);
                expected_first_set.insert("A",     a_first);
                expected_first_set.insert("B",     b_first);

                assert!(first_set == expected_first_set);
            },
        }
    }
}

#[cfg(test)]
mod get_follow_set {
    use super::*;

    #[test]
    fn combo_e() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Empty],
        ]);

        let first_set               = get_first_set(&grammar).unwrap();
        let mut expected_follow_set = BTreeMap::new();

        expected_follow_set.insert("START", BTreeSet::new());
        expected_follow_set.insert("A",     BTreeSet::new());

        assert!(get_follow_set(&grammar, &first_set) == expected_follow_set);
    }

    #[test]
    fn combo_t() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Terminal('b')],
        ]);

        let first_set               = get_first_set(&grammar).unwrap();
        let mut expected_follow_set = BTreeMap::new();

        expected_follow_set.insert("START", BTreeSet::new());
        expected_follow_set.insert("A",     BTreeSet::new());

        assert!(get_follow_set(&grammar, &first_set) == expected_follow_set);
    }

    #[test]
    fn combo_n_e() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::NonTerminal("B")],
        ]);

        grammar.insert("B", vec![
            vec![RuleElement::Empty],
        ]);

        let first_set               = get_first_set(&grammar).unwrap();
        let mut expected_follow_set = BTreeMap::new();

        expected_follow_set.insert("START", BTreeSet::new());
        expected_follow_set.insert("A",     BTreeSet::new());
        expected_follow_set.insert("B",     BTreeSet::new());

        assert!(get_follow_set(&grammar, &first_set) == expected_follow_set);
    }

    #[test]
    fn combo_n_t() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::NonTerminal("B")],
        ]);

        grammar.insert("B", vec![
            vec![RuleElement::Terminal('c')],
        ]);

        let first_set               = get_first_set(&grammar).unwrap();
        let mut expected_follow_set = BTreeMap::new();

        expected_follow_set.insert("START", BTreeSet::new());
        expected_follow_set.insert("A",     BTreeSet::new());
        expected_follow_set.insert("B",     BTreeSet::new());

        assert!(get_follow_set(&grammar, &first_set) == expected_follow_set);
    }

    #[test]
    fn combo_ee() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Empty, RuleElement::Empty],
        ]);

        let first_set               = get_first_set(&grammar).unwrap();
        let mut expected_follow_set = BTreeMap::new();

        expected_follow_set.insert("START", BTreeSet::new());
        expected_follow_set.insert("A",     BTreeSet::new());

        assert!(get_follow_set(&grammar, &first_set) == expected_follow_set);
    }

    #[test]
    fn combo_et() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Empty, RuleElement::Terminal('b')],
        ]);

        let first_set               = get_first_set(&grammar).unwrap();
        let mut expected_follow_set = BTreeMap::new();

        expected_follow_set.insert("START", BTreeSet::new());
        expected_follow_set.insert("A",     BTreeSet::new());

        assert!(get_follow_set(&grammar, &first_set) == expected_follow_set);
    }

    #[test]
    fn combo_en_e() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Empty, RuleElement::NonTerminal("B")],
        ]);

        grammar.insert("B", vec![
            vec![RuleElement::Empty],
        ]);

        let first_set               = get_first_set(&grammar).unwrap();
        let mut expected_follow_set = BTreeMap::new();

        expected_follow_set.insert("START", BTreeSet::new());
        expected_follow_set.insert("A",     BTreeSet::new());
        expected_follow_set.insert("B",     BTreeSet::new());

        assert!(get_follow_set(&grammar, &first_set) == expected_follow_set);
    }

    #[test]
    fn combo_en_t() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Empty, RuleElement::NonTerminal("B")],
        ]);

        grammar.insert("B", vec![
            vec![RuleElement::Terminal('c')],
        ]);

        let first_set               = get_first_set(&grammar).unwrap();
        let mut expected_follow_set = BTreeMap::new();

        expected_follow_set.insert("START", BTreeSet::new());
        expected_follow_set.insert("A",     BTreeSet::new());
        expected_follow_set.insert("B",     BTreeSet::new());

        assert!(get_follow_set(&grammar, &first_set) == expected_follow_set);
    }

    #[test]
    fn combo_eee() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Empty, RuleElement::Empty, RuleElement::Empty],
        ]);

        let first_set               = get_first_set(&grammar).unwrap();
        let mut expected_follow_set = BTreeMap::new();

        expected_follow_set.insert("START", BTreeSet::new());
        expected_follow_set.insert("A",     BTreeSet::new());

        assert!(get_follow_set(&grammar, &first_set) == expected_follow_set);
    }

    #[test]
    fn combo_eet() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Empty, RuleElement::Empty, RuleElement::Terminal('b')],
        ]);

        let first_set               = get_first_set(&grammar).unwrap();
        let mut expected_follow_set = BTreeMap::new();

        expected_follow_set.insert("START", BTreeSet::new());
        expected_follow_set.insert("A",     BTreeSet::new());

        assert!(get_follow_set(&grammar, &first_set) == expected_follow_set);
    }

    #[test]
    fn combo_een_e() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Empty, RuleElement::Empty, RuleElement::NonTerminal("B")],
        ]);

        grammar.insert("B", vec![
            vec![RuleElement::Empty],
        ]);

        let first_set               = get_first_set(&grammar).unwrap();
        let mut expected_follow_set = BTreeMap::new();

        expected_follow_set.insert("START", BTreeSet::new());
        expected_follow_set.insert("A",     BTreeSet::new());
        expected_follow_set.insert("B",     BTreeSet::new());

        assert!(get_follow_set(&grammar, &first_set) == expected_follow_set);
    }

    #[test]
    fn combo_een_t() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Empty, RuleElement::Empty, RuleElement::NonTerminal("B")],
        ]);

        grammar.insert("B", vec![
            vec![RuleElement::Terminal('c')],
        ]);

        let first_set               = get_first_set(&grammar).unwrap();
        let mut expected_follow_set = BTreeMap::new();

        expected_follow_set.insert("START", BTreeSet::new());
        expected_follow_set.insert("A",     BTreeSet::new());
        expected_follow_set.insert("B",     BTreeSet::new());

        assert!(get_follow_set(&grammar, &first_set) == expected_follow_set);
    }

    #[test]
    fn combo_ete() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Empty, RuleElement::Terminal('b'), RuleElement::Empty],
        ]);

        let first_set               = get_first_set(&grammar).unwrap();
        let mut expected_follow_set = BTreeMap::new();

        expected_follow_set.insert("START", BTreeSet::new());
        expected_follow_set.insert("A",     BTreeSet::new());

        assert!(get_follow_set(&grammar, &first_set) == expected_follow_set);
    }

    #[test]
    fn combo_ett() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Empty, RuleElement::Terminal('b'), RuleElement::Terminal('c')],
        ]);

        let first_set               = get_first_set(&grammar).unwrap();
        let mut expected_follow_set = BTreeMap::new();

        expected_follow_set.insert("START", BTreeSet::new());
        expected_follow_set.insert("A",     BTreeSet::new());

        assert!(get_follow_set(&grammar, &first_set) == expected_follow_set);
    }

    #[test]
    fn combo_etn_e() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Empty, RuleElement::Terminal('b'), RuleElement::NonTerminal("C")],
        ]);

        grammar.insert("C", vec![
            vec![RuleElement::Empty],
        ]);

        let first_set               = get_first_set(&grammar).unwrap();
        let mut expected_follow_set = BTreeMap::new();

        expected_follow_set.insert("START", BTreeSet::new());
        expected_follow_set.insert("A",     BTreeSet::new());
        expected_follow_set.insert("C",     BTreeSet::new());

        assert!(get_follow_set(&grammar, &first_set) == expected_follow_set);
    }

    #[test]
    fn combo_etn_t() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Empty, RuleElement::Terminal('b'), RuleElement::NonTerminal("C")],
        ]);

        grammar.insert("C", vec![
            vec![RuleElement::Terminal('d')],
        ]);

        let first_set               = get_first_set(&grammar).unwrap();
        let mut expected_follow_set = BTreeMap::new();

        expected_follow_set.insert("START", BTreeSet::new());
        expected_follow_set.insert("A",     BTreeSet::new());
        expected_follow_set.insert("C",     BTreeSet::new());

        assert!(get_follow_set(&grammar, &first_set) == expected_follow_set);
    }

    #[test]
    fn combo_ene_e() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Empty, RuleElement::NonTerminal("B"), RuleElement::Empty],
        ]);

        grammar.insert("B", vec![
            vec![RuleElement::Empty],
        ]);

        let first_set               = get_first_set(&grammar).unwrap();
        let mut expected_follow_set = BTreeMap::new();

        expected_follow_set.insert("START", BTreeSet::new());
        expected_follow_set.insert("A",     BTreeSet::new());
        expected_follow_set.insert("B",     BTreeSet::new());

        assert!(get_follow_set(&grammar, &first_set) == expected_follow_set);
    }

    #[test]
    fn combo_ene_t() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Empty, RuleElement::NonTerminal("B"), RuleElement::Empty],
        ]);

        grammar.insert("B", vec![
            vec![RuleElement::Terminal('c')],
        ]);

        let first_set               = get_first_set(&grammar).unwrap();
        let mut expected_follow_set = BTreeMap::new();

        expected_follow_set.insert("START", BTreeSet::new());
        expected_follow_set.insert("A",     BTreeSet::new());
        expected_follow_set.insert("B",     BTreeSet::new());

        assert!(get_follow_set(&grammar, &first_set) == expected_follow_set);
    }

    #[test]
    fn combo_ent_e() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Empty, RuleElement::NonTerminal("B"), RuleElement::Terminal('c')],
        ]);

        grammar.insert("B", vec![
            vec![RuleElement::Empty],
        ]);

        let first_set               = get_first_set(&grammar).unwrap();
        let mut expected_follow_set = BTreeMap::new();

        let mut b_follow = BTreeSet::new();
        b_follow.insert('c');

        expected_follow_set.insert("START", BTreeSet::new());
        expected_follow_set.insert("A",     BTreeSet::new());
        expected_follow_set.insert("B",     b_follow);

        assert!(get_follow_set(&grammar, &first_set) == expected_follow_set);
    }

    #[test]
    fn combo_ent_t() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Empty, RuleElement::NonTerminal("B"), RuleElement::Terminal('c')],
        ]);

        grammar.insert("B", vec![
            vec![RuleElement::Terminal('d')],
        ]);

        let first_set               = get_first_set(&grammar).unwrap();
        let mut expected_follow_set = BTreeMap::new();

        let mut b_follow = BTreeSet::new();
        b_follow.insert('c');

        expected_follow_set.insert("START", BTreeSet::new());
        expected_follow_set.insert("A",     BTreeSet::new());
        expected_follow_set.insert("B",     b_follow);

        assert!(get_follow_set(&grammar, &first_set) == expected_follow_set);
    }

    #[test]
    fn combo_enn_e() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Empty, RuleElement::NonTerminal("B"), RuleElement::NonTerminal("C")],
        ]);

        grammar.insert("B", vec![
            vec![RuleElement::Empty],
        ]);

        grammar.insert("C", vec![
            vec![RuleElement::Empty],
        ]);

        let first_set               = get_first_set(&grammar).unwrap();
        let mut expected_follow_set = BTreeMap::new();

        expected_follow_set.insert("START", BTreeSet::new());
        expected_follow_set.insert("A",     BTreeSet::new());
        expected_follow_set.insert("B",     BTreeSet::new());
        expected_follow_set.insert("C",     BTreeSet::new());

        assert!(get_follow_set(&grammar, &first_set) == expected_follow_set);
    }

    #[test]
    fn combo_enn_t() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Empty, RuleElement::NonTerminal("B"), RuleElement::NonTerminal("C")],
        ]);

        grammar.insert("B", vec![
            vec![RuleElement::Empty],
        ]);

        grammar.insert("C", vec![
            vec![RuleElement::Terminal('d')],
        ]);

        let first_set               = get_first_set(&grammar).unwrap();
        let mut expected_follow_set = BTreeMap::new();

        let mut b_follow = BTreeSet::new();
        b_follow.insert('d');

        expected_follow_set.insert("START", BTreeSet::new());
        expected_follow_set.insert("A",     BTreeSet::new());
        expected_follow_set.insert("B",     b_follow);
        expected_follow_set.insert("C",     BTreeSet::new());

        assert!(get_follow_set(&grammar, &first_set) == expected_follow_set);
    }

    #[test]
    fn combo_te() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Terminal('b'), RuleElement::Empty],
        ]);

        let first_set               = get_first_set(&grammar).unwrap();
        let mut expected_follow_set = BTreeMap::new();

        expected_follow_set.insert("START", BTreeSet::new());
        expected_follow_set.insert("A",     BTreeSet::new());

        assert!(get_follow_set(&grammar, &first_set) == expected_follow_set);
    }

    #[test]
    fn combo_tt() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Terminal('b'), RuleElement::Terminal('c')],
        ]);

        let first_set               = get_first_set(&grammar).unwrap();
        let mut expected_follow_set = BTreeMap::new();

        expected_follow_set.insert("START", BTreeSet::new());
        expected_follow_set.insert("A",     BTreeSet::new());

        assert!(get_follow_set(&grammar, &first_set) == expected_follow_set);
    }

    #[test]
    fn combo_tn_e() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Terminal('b'), RuleElement::NonTerminal("C")],
        ]);

        grammar.insert("C", vec![
            vec![RuleElement::Empty],
        ]);

        let first_set               = get_first_set(&grammar).unwrap();
        let mut expected_follow_set = BTreeMap::new();

        expected_follow_set.insert("START", BTreeSet::new());
        expected_follow_set.insert("A",     BTreeSet::new());
        expected_follow_set.insert("C",     BTreeSet::new());

        assert!(get_follow_set(&grammar, &first_set) == expected_follow_set);
    }

    #[test]
    fn combo_tn_t() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Terminal('b'), RuleElement::NonTerminal("C")],
        ]);

        grammar.insert("C", vec![
            vec![RuleElement::Terminal('d')],
        ]);

        let first_set               = get_first_set(&grammar).unwrap();
        let mut expected_follow_set = BTreeMap::new();

        expected_follow_set.insert("START", BTreeSet::new());
        expected_follow_set.insert("A",     BTreeSet::new());
        expected_follow_set.insert("C",     BTreeSet::new());

        assert!(get_follow_set(&grammar, &first_set) == expected_follow_set);
    }

    #[test]
    fn combo_tee() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Terminal('b'), RuleElement::Empty, RuleElement::Empty],
        ]);

        let first_set               = get_first_set(&grammar).unwrap();
        let mut expected_follow_set = BTreeMap::new();

        expected_follow_set.insert("START", BTreeSet::new());
        expected_follow_set.insert("A",     BTreeSet::new());

        assert!(get_follow_set(&grammar, &first_set) == expected_follow_set);
    }

    #[test]
    fn combo_tet() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Terminal('b'), RuleElement::Empty, RuleElement::Terminal('c')],
        ]);

        let first_set               = get_first_set(&grammar).unwrap();
        let mut expected_follow_set = BTreeMap::new();

        expected_follow_set.insert("START", BTreeSet::new());
        expected_follow_set.insert("A",     BTreeSet::new());

        assert!(get_follow_set(&grammar, &first_set) == expected_follow_set);
    }

    #[test]
    fn combo_ten_e() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Terminal('b'), RuleElement::Empty, RuleElement::NonTerminal("C")],
        ]);

        grammar.insert("C", vec![
            vec![RuleElement::Empty],
        ]);

        let first_set               = get_first_set(&grammar).unwrap();
        let mut expected_follow_set = BTreeMap::new();

        expected_follow_set.insert("START", BTreeSet::new());
        expected_follow_set.insert("A",     BTreeSet::new());
        expected_follow_set.insert("C",     BTreeSet::new());

        assert!(get_follow_set(&grammar, &first_set) == expected_follow_set);
    }

    #[test]
    fn combo_ten_t() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Terminal('b'), RuleElement::Empty, RuleElement::NonTerminal("C")],
        ]);

        grammar.insert("C", vec![
            vec![RuleElement::Terminal('d')],
        ]);

        let first_set               = get_first_set(&grammar).unwrap();
        let mut expected_follow_set = BTreeMap::new();

        expected_follow_set.insert("START", BTreeSet::new());
        expected_follow_set.insert("A",     BTreeSet::new());
        expected_follow_set.insert("C",     BTreeSet::new());

        assert!(get_follow_set(&grammar, &first_set) == expected_follow_set);
    }

    #[test]
    fn combo_tte() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Terminal('b'), RuleElement::Terminal('c'), RuleElement::Empty],
        ]);

        let first_set               = get_first_set(&grammar).unwrap();
        let mut expected_follow_set = BTreeMap::new();

        expected_follow_set.insert("START", BTreeSet::new());
        expected_follow_set.insert("A",     BTreeSet::new());

        assert!(get_follow_set(&grammar, &first_set) == expected_follow_set);
    }

    #[test]
    fn combo_ttt() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Terminal('b'), RuleElement::Terminal('c'), RuleElement::Terminal('d')],
        ]);

        let first_set               = get_first_set(&grammar).unwrap();
        let mut expected_follow_set = BTreeMap::new();

        expected_follow_set.insert("START", BTreeSet::new());
        expected_follow_set.insert("A",     BTreeSet::new());

        assert!(get_follow_set(&grammar, &first_set) == expected_follow_set);
    }

    #[test]
    fn combo_ttn_e() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Terminal('b'), RuleElement::Terminal('c'), RuleElement::NonTerminal("D")],
        ]);

        grammar.insert("D", vec![
            vec![RuleElement::Empty],
        ]);

        let first_set               = get_first_set(&grammar).unwrap();
        let mut expected_follow_set = BTreeMap::new();

        expected_follow_set.insert("START", BTreeSet::new());
        expected_follow_set.insert("A",     BTreeSet::new());
        expected_follow_set.insert("D",     BTreeSet::new());

        assert!(get_follow_set(&grammar, &first_set) == expected_follow_set);
    }

    #[test]
    fn combo_ttn_t() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Terminal('b'), RuleElement::Terminal('c'), RuleElement::NonTerminal("D")],
        ]);

        grammar.insert("D", vec![
            vec![RuleElement::Terminal('e')],
        ]);

        let first_set               = get_first_set(&grammar).unwrap();
        let mut expected_follow_set = BTreeMap::new();

        expected_follow_set.insert("START", BTreeSet::new());
        expected_follow_set.insert("A",     BTreeSet::new());
        expected_follow_set.insert("D",     BTreeSet::new());

        assert!(get_follow_set(&grammar, &first_set) == expected_follow_set);
    }

    #[test]
    fn combo_tne_e() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Terminal('b'), RuleElement::NonTerminal("C"), RuleElement::Empty],
        ]);

        grammar.insert("C", vec![
            vec![RuleElement::Empty],
        ]);

        let first_set               = get_first_set(&grammar).unwrap();
        let mut expected_follow_set = BTreeMap::new();

        expected_follow_set.insert("START", BTreeSet::new());
        expected_follow_set.insert("A",     BTreeSet::new());
        expected_follow_set.insert("C",     BTreeSet::new());

        assert!(get_follow_set(&grammar, &first_set) == expected_follow_set);
    }

    #[test]
    fn combo_tne_t() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Terminal('b'), RuleElement::NonTerminal("C"), RuleElement::Empty],
        ]);

        grammar.insert("C", vec![
            vec![RuleElement::Terminal('d')],
        ]);

        let first_set               = get_first_set(&grammar).unwrap();
        let mut expected_follow_set = BTreeMap::new();

        expected_follow_set.insert("START", BTreeSet::new());
        expected_follow_set.insert("A",     BTreeSet::new());
        expected_follow_set.insert("C",     BTreeSet::new());

        assert!(get_follow_set(&grammar, &first_set) == expected_follow_set);
    }

    #[test]
    fn combo_tnt_e() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Terminal('b'), RuleElement::NonTerminal("C"), RuleElement::Terminal('d')],
        ]);

        grammar.insert("C", vec![
            vec![RuleElement::Empty],
        ]);

        let first_set               = get_first_set(&grammar).unwrap();
        let mut expected_follow_set = BTreeMap::new();

        let mut c_follow = BTreeSet::new();
        c_follow.insert('d');

        expected_follow_set.insert("START", BTreeSet::new());
        expected_follow_set.insert("A",     BTreeSet::new());
        expected_follow_set.insert("C",     c_follow);

        assert!(get_follow_set(&grammar, &first_set) == expected_follow_set);
    }

    #[test]
    fn combo_tnt_t() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Terminal('b'), RuleElement::NonTerminal("C"), RuleElement::Terminal('d')],
        ]);

        grammar.insert("C", vec![
            vec![RuleElement::Terminal('e')],
        ]);

        let first_set               = get_first_set(&grammar).unwrap();
        let mut expected_follow_set = BTreeMap::new();

        let mut c_follow = BTreeSet::new();
        c_follow.insert('d');

        expected_follow_set.insert("START", BTreeSet::new());
        expected_follow_set.insert("A",     BTreeSet::new());
        expected_follow_set.insert("C",     c_follow);

        assert!(get_follow_set(&grammar, &first_set) == expected_follow_set);
    }

    #[test]
    fn combo_tnn_e() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Terminal('b'), RuleElement::NonTerminal("C"), RuleElement::NonTerminal("D")],
        ]);

        grammar.insert("C", vec![
            vec![RuleElement::Empty],
        ]);

        grammar.insert("D", vec![
            vec![RuleElement::Empty],
        ]);

        let first_set               = get_first_set(&grammar).unwrap();
        let mut expected_follow_set = BTreeMap::new();

        expected_follow_set.insert("START", BTreeSet::new());
        expected_follow_set.insert("A",     BTreeSet::new());
        expected_follow_set.insert("C",     BTreeSet::new());
        expected_follow_set.insert("D",     BTreeSet::new());

        assert!(get_follow_set(&grammar, &first_set) == expected_follow_set);
    }

    #[test]
    fn combo_tnn_t() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Terminal('b'), RuleElement::NonTerminal("C"), RuleElement::NonTerminal("D")],
        ]);

        grammar.insert("C", vec![
            vec![RuleElement::Empty],
        ]);

        grammar.insert("D", vec![
            vec![RuleElement::Terminal('e')],
        ]);

        let first_set               = get_first_set(&grammar).unwrap();
        let mut expected_follow_set = BTreeMap::new();

        let mut c_follow = BTreeSet::new();
        c_follow.insert('e');

        expected_follow_set.insert("START", BTreeSet::new());
        expected_follow_set.insert("A",     BTreeSet::new());
        expected_follow_set.insert("C",     c_follow);
        expected_follow_set.insert("D",     BTreeSet::new());

        assert!(get_follow_set(&grammar, &first_set) == expected_follow_set);
    }

    #[test]
    fn combo_nee_e() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::NonTerminal("B"), RuleElement::Empty, RuleElement::Empty],
        ]);

        grammar.insert("B", vec![
            vec![RuleElement::Empty],
        ]);

        let first_set               = get_first_set(&grammar).unwrap();
        let mut expected_follow_set = BTreeMap::new();

        expected_follow_set.insert("START", BTreeSet::new());
        expected_follow_set.insert("A",     BTreeSet::new());
        expected_follow_set.insert("B",     BTreeSet::new());

        assert!(get_follow_set(&grammar, &first_set) == expected_follow_set);
    }

    #[test]
    fn combo_nee_t() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::NonTerminal("B"), RuleElement::Empty, RuleElement::Empty],
        ]);

        grammar.insert("B", vec![
            vec![RuleElement::Terminal('c')],
        ]);

        let first_set               = get_first_set(&grammar).unwrap();
        let mut expected_follow_set = BTreeMap::new();

        expected_follow_set.insert("START", BTreeSet::new());
        expected_follow_set.insert("A",     BTreeSet::new());
        expected_follow_set.insert("B",     BTreeSet::new());

        assert!(get_follow_set(&grammar, &first_set) == expected_follow_set);
    }

    #[test]
    fn combo_net_e() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::NonTerminal("B"), RuleElement::Empty, RuleElement::Terminal('c')],
        ]);

        grammar.insert("B", vec![
            vec![RuleElement::Empty],
        ]);

        let first_set               = get_first_set(&grammar).unwrap();
        let mut expected_follow_set = BTreeMap::new();

        let mut b_follow = BTreeSet::new();
        b_follow.insert('c');

        expected_follow_set.insert("START", BTreeSet::new());
        expected_follow_set.insert("A",     BTreeSet::new());
        expected_follow_set.insert("B",     b_follow);

        assert!(get_follow_set(&grammar, &first_set) == expected_follow_set);
    }

    #[test]
    fn combo_net_t() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::NonTerminal("B"), RuleElement::Empty, RuleElement::Terminal('c')],
        ]);

        grammar.insert("B", vec![
            vec![RuleElement::Terminal('d')],
        ]);

        let first_set               = get_first_set(&grammar).unwrap();
        let mut expected_follow_set = BTreeMap::new();

        let mut b_follow = BTreeSet::new();
        b_follow.insert('c');

        expected_follow_set.insert("START", BTreeSet::new());
        expected_follow_set.insert("A",     BTreeSet::new());
        expected_follow_set.insert("B",     b_follow);

        assert!(get_follow_set(&grammar, &first_set) == expected_follow_set);
    }

    #[test]
    fn combo_nen_e() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::NonTerminal("B"), RuleElement::Empty, RuleElement::NonTerminal("C")],
        ]);

        grammar.insert("B", vec![
            vec![RuleElement::Empty],
        ]);

        grammar.insert("C", vec![
            vec![RuleElement::Empty],
        ]);

        let first_set               = get_first_set(&grammar).unwrap();
        let mut expected_follow_set = BTreeMap::new();

        expected_follow_set.insert("START", BTreeSet::new());
        expected_follow_set.insert("A",     BTreeSet::new());
        expected_follow_set.insert("B",     BTreeSet::new());
        expected_follow_set.insert("C",     BTreeSet::new());

        assert!(get_follow_set(&grammar, &first_set) == expected_follow_set);
    }

    #[test]
    fn combo_nen_t() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::NonTerminal("B"), RuleElement::Empty, RuleElement::NonTerminal("C")],
        ]);

        grammar.insert("B", vec![
            vec![RuleElement::Empty],
        ]);

        grammar.insert("C", vec![
            vec![RuleElement::Terminal('d')],
        ]);

        let first_set               = get_first_set(&grammar).unwrap();
        let mut expected_follow_set = BTreeMap::new();

        let mut b_follow = BTreeSet::new();
        b_follow.insert('d');

        expected_follow_set.insert("START", BTreeSet::new());
        expected_follow_set.insert("A",     BTreeSet::new());
        expected_follow_set.insert("B",     b_follow);
        expected_follow_set.insert("C",     BTreeSet::new());

        assert!(get_follow_set(&grammar, &first_set) == expected_follow_set);
    }

    #[test]
    fn combo_nte_e() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::NonTerminal("B"), RuleElement::Empty, RuleElement::Empty],
        ]);

        grammar.insert("B", vec![
            vec![RuleElement::Empty],
        ]);

        let first_set               = get_first_set(&grammar).unwrap();
        let mut expected_follow_set = BTreeMap::new();

        expected_follow_set.insert("START", BTreeSet::new());
        expected_follow_set.insert("A",     BTreeSet::new());
        expected_follow_set.insert("B",     BTreeSet::new());

        assert!(get_follow_set(&grammar, &first_set) == expected_follow_set);
    }

    #[test]
    fn combo_nte_t() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::NonTerminal("B"), RuleElement::Empty, RuleElement::Empty],
        ]);

        grammar.insert("B", vec![
            vec![RuleElement::Terminal('c')],
        ]);

        let first_set               = get_first_set(&grammar).unwrap();
        let mut expected_follow_set = BTreeMap::new();

        expected_follow_set.insert("START", BTreeSet::new());
        expected_follow_set.insert("A",     BTreeSet::new());
        expected_follow_set.insert("B",     BTreeSet::new());

        assert!(get_follow_set(&grammar, &first_set) == expected_follow_set);
    }

    #[test]
    fn combo_ntt_e() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::NonTerminal("B"), RuleElement::Terminal('c'), RuleElement::Terminal('d')],
        ]);

        grammar.insert("B", vec![
            vec![RuleElement::Empty],
        ]);

        let first_set               = get_first_set(&grammar).unwrap();
        let mut expected_follow_set = BTreeMap::new();

        let mut b_follow = BTreeSet::new();
        b_follow.insert('c');

        expected_follow_set.insert("START", BTreeSet::new());
        expected_follow_set.insert("A",     BTreeSet::new());
        expected_follow_set.insert("B",     b_follow);

        assert!(get_follow_set(&grammar, &first_set) == expected_follow_set);
    }

    #[test]
    fn combo_ntt_t() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::NonTerminal("B"), RuleElement::Terminal('c'), RuleElement::Terminal('d')],
        ]);

        grammar.insert("B", vec![
            vec![RuleElement::Terminal('e')],
        ]);

        let first_set               = get_first_set(&grammar).unwrap();
        let mut expected_follow_set = BTreeMap::new();

        let mut b_follow = BTreeSet::new();
        b_follow.insert('c');

        expected_follow_set.insert("START", BTreeSet::new());
        expected_follow_set.insert("A",     BTreeSet::new());
        expected_follow_set.insert("B",     b_follow);

        assert!(get_follow_set(&grammar, &first_set) == expected_follow_set);
    }

    #[test]
    fn combo_ntn_e() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::NonTerminal("B"), RuleElement::Terminal('c'), RuleElement::NonTerminal("C")],
        ]);

        grammar.insert("B", vec![
            vec![RuleElement::Empty],
        ]);

        grammar.insert("C", vec![
            vec![RuleElement::Empty],
        ]);

        let first_set               = get_first_set(&grammar).unwrap();
        let mut expected_follow_set = BTreeMap::new();

        let mut b_follow = BTreeSet::new();
        b_follow.insert('c');

        expected_follow_set.insert("START", BTreeSet::new());
        expected_follow_set.insert("A",     BTreeSet::new());
        expected_follow_set.insert("B",     b_follow);
        expected_follow_set.insert("C",     BTreeSet::new());

        assert!(get_follow_set(&grammar, &first_set) == expected_follow_set);
    }

    #[test]
    fn combo_ntn_t() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::NonTerminal("B"), RuleElement::Terminal('c'), RuleElement::NonTerminal("C")],
        ]);

        grammar.insert("B", vec![
            vec![RuleElement::Empty],
        ]);

        grammar.insert("C", vec![
            vec![RuleElement::Terminal('d')],
        ]);

        let first_set               = get_first_set(&grammar).unwrap();
        let mut expected_follow_set = BTreeMap::new();

        let mut b_follow = BTreeSet::new();
        b_follow.insert('c');

        expected_follow_set.insert("START", BTreeSet::new());
        expected_follow_set.insert("A",     BTreeSet::new());
        expected_follow_set.insert("B",     b_follow);
        expected_follow_set.insert("C",     BTreeSet::new());

        assert!(get_follow_set(&grammar, &first_set) == expected_follow_set);
    }

    #[test]
    fn combo_nne() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::NonTerminal("B"), RuleElement::NonTerminal("C"), RuleElement::Empty],
        ]);

        grammar.insert("B", vec![
            vec![RuleElement::Empty],
        ]);

        grammar.insert("C", vec![
            vec![RuleElement::Empty],
        ]);

        let first_set               = get_first_set(&grammar).unwrap();
        let mut expected_follow_set = BTreeMap::new();

        expected_follow_set.insert("START", BTreeSet::new());
        expected_follow_set.insert("A",     BTreeSet::new());
        expected_follow_set.insert("B",     BTreeSet::new());
        expected_follow_set.insert("C",     BTreeSet::new());

        assert!(get_follow_set(&grammar, &first_set) == expected_follow_set);
    }

    #[test]
    fn combo_nne_t() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::NonTerminal("B"), RuleElement::NonTerminal("C"), RuleElement::Empty],
        ]);

        grammar.insert("B", vec![
            vec![RuleElement::Empty],
        ]);

        grammar.insert("C", vec![
            vec![RuleElement::Terminal('d')],
        ]);

        let first_set               = get_first_set(&grammar).unwrap();
        let mut expected_follow_set = BTreeMap::new();

        let mut b_follow = BTreeSet::new();
        b_follow.insert('d');

        expected_follow_set.insert("START", BTreeSet::new());
        expected_follow_set.insert("A",     BTreeSet::new());
        expected_follow_set.insert("B",     b_follow);
        expected_follow_set.insert("C",     BTreeSet::new());

        assert!(get_follow_set(&grammar, &first_set) == expected_follow_set);
    }

    #[test]
    fn combo_nnt_e() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::NonTerminal("B"), RuleElement::NonTerminal("C"), RuleElement::Terminal('d')],
        ]);

        grammar.insert("B", vec![
            vec![RuleElement::Empty],
        ]);

        grammar.insert("C", vec![
            vec![RuleElement::Empty],
        ]);

        let first_set               = get_first_set(&grammar).unwrap();
        let mut expected_follow_set = BTreeMap::new();

        let mut b_follow = BTreeSet::new();
        b_follow.insert('d');

        let mut c_follow = BTreeSet::new();
        c_follow.insert('d');

        expected_follow_set.insert("START", BTreeSet::new());
        expected_follow_set.insert("A",     BTreeSet::new());
        expected_follow_set.insert("B",     b_follow);
        expected_follow_set.insert("C",     c_follow);

        assert!(get_follow_set(&grammar, &first_set) == expected_follow_set);
    }

    #[test]
    fn combo_nnt_t() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::NonTerminal("B"), RuleElement::NonTerminal("C"), RuleElement::Terminal('d')],
        ]);

        grammar.insert("B", vec![
            vec![RuleElement::Empty],
        ]);

        grammar.insert("C", vec![
            vec![RuleElement::Terminal('e')],
        ]);

        let first_set               = get_first_set(&grammar).unwrap();
        let mut expected_follow_set = BTreeMap::new();

        let mut b_follow = BTreeSet::new();
        b_follow.insert('e');

        let mut c_follow = BTreeSet::new();
        c_follow.insert('d');

        expected_follow_set.insert("START", BTreeSet::new());
        expected_follow_set.insert("A",     BTreeSet::new());
        expected_follow_set.insert("B",     b_follow);
        expected_follow_set.insert("C",     c_follow);

        assert!(get_follow_set(&grammar, &first_set) == expected_follow_set);
    }

    #[test]
    fn combo_nnn_e() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::NonTerminal("B"), RuleElement::NonTerminal("C"), RuleElement::NonTerminal("D")],
        ]);

        grammar.insert("B", vec![
            vec![RuleElement::Empty],
        ]);

        grammar.insert("C", vec![
            vec![RuleElement::Empty],
        ]);

        grammar.insert("D", vec![
            vec![RuleElement::Empty],
        ]);

        let first_set               = get_first_set(&grammar).unwrap();
        let mut expected_follow_set = BTreeMap::new();

        expected_follow_set.insert("START", BTreeSet::new());
        expected_follow_set.insert("A",     BTreeSet::new());
        expected_follow_set.insert("B",     BTreeSet::new());
        expected_follow_set.insert("C",     BTreeSet::new());
        expected_follow_set.insert("D",     BTreeSet::new());

        assert!(get_follow_set(&grammar, &first_set) == expected_follow_set);
    }

    #[test]
    fn combo_nnn_t_e() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::NonTerminal("B"), RuleElement::NonTerminal("C"), RuleElement::NonTerminal("D")],
        ]);

        grammar.insert("B", vec![
            vec![RuleElement::Empty],
        ]);

        grammar.insert("C", vec![
            vec![RuleElement::Terminal('e')],
        ]);

        grammar.insert("D", vec![
            vec![RuleElement::Empty],
        ]);

        let first_set               = get_first_set(&grammar).unwrap();
        let mut expected_follow_set = BTreeMap::new();

        let mut b_follow = BTreeSet::new();
        b_follow.insert('e');

        expected_follow_set.insert("START", BTreeSet::new());
        expected_follow_set.insert("A",     BTreeSet::new());
        expected_follow_set.insert("B",     b_follow);
        expected_follow_set.insert("C",     BTreeSet::new());
        expected_follow_set.insert("D",     BTreeSet::new());

        assert!(get_follow_set(&grammar, &first_set) == expected_follow_set);
    }

    #[test]
    fn combo_nnn_t_t() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::NonTerminal("B"), RuleElement::NonTerminal("C"), RuleElement::NonTerminal("D")],
        ]);

        grammar.insert("B", vec![
            vec![RuleElement::Empty],
        ]);

        grammar.insert("C", vec![
            vec![RuleElement::Terminal('e')],
        ]);

        grammar.insert("D", vec![
            vec![RuleElement::Terminal('f')],
        ]);

        let first_set               = get_first_set(&grammar).unwrap();
        let mut expected_follow_set = BTreeMap::new();

        let mut b_follow = BTreeSet::new();
        b_follow.insert('e');

        let mut c_follow = BTreeSet::new();
        c_follow.insert('f');

        expected_follow_set.insert("START", BTreeSet::new());
        expected_follow_set.insert("A",     BTreeSet::new());
        expected_follow_set.insert("B",     b_follow);
        expected_follow_set.insert("C",     c_follow);
        expected_follow_set.insert("D",     BTreeSet::new());

        assert!(get_follow_set(&grammar, &first_set) == expected_follow_set);
    }
}

#[cfg(test)]
mod get_parse_table {
    use super::*;

    #[test]
    fn combo_e() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Empty],
        ]);

        let first_set  = get_first_set(&grammar).unwrap();
        let follow_set = get_follow_set(&grammar, &first_set);

        let mut expected_parse_table = BTreeMap::new();
        expected_parse_table.insert("START", BTreeMap::new());
        expected_parse_table.insert("A",     BTreeMap::new());

        assert!(expected_parse_table == get_parse_table(&grammar, &first_set, &follow_set).unwrap());
    }

    #[test]
    fn combo_ee() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Empty, RuleElement::Empty],
        ]);

        let first_set  = get_first_set(&grammar).unwrap();
        let follow_set = get_follow_set(&grammar, &first_set);

        let mut expected_parse_table = BTreeMap::new();
        expected_parse_table.insert("START", BTreeMap::new());
        expected_parse_table.insert("A",     BTreeMap::new());

        assert!(expected_parse_table == get_parse_table(&grammar, &first_set, &follow_set).unwrap());
    }

    #[test]
    fn combo_et() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Empty, RuleElement::Terminal('b')],
        ]);

        let first_set  = get_first_set(&grammar).unwrap();
        let follow_set = get_follow_set(&grammar, &first_set);

        let mut start_parse = BTreeMap::new();
        start_parse.insert('b', vec![RuleElement::NonTerminal("A")]);

        let mut a_parse = BTreeMap::new();
        a_parse.insert('b', vec![RuleElement::Empty, RuleElement::Terminal('b')]);

        let mut expected_parse_table = BTreeMap::new();
        expected_parse_table.insert("START", start_parse);
        expected_parse_table.insert("A",     a_parse);

        assert!(expected_parse_table == get_parse_table(&grammar, &first_set, &follow_set).unwrap());
    }

    #[test]
    fn combo_en_e() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Empty, RuleElement::NonTerminal("B")],
        ]);

        grammar.insert("B", vec![
            vec![RuleElement::Empty],
        ]);

        let first_set  = get_first_set(&grammar).unwrap();
        let follow_set = get_follow_set(&grammar, &first_set);

        let mut expected_parse_table = BTreeMap::new();
        expected_parse_table.insert("START", BTreeMap::new());
        expected_parse_table.insert("A",     BTreeMap::new());
        expected_parse_table.insert("B",     BTreeMap::new());

        assert!(expected_parse_table == get_parse_table(&grammar, &first_set, &follow_set).unwrap());
    }

    #[test]
    fn combo_en_t() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Empty, RuleElement::NonTerminal("B")],
        ]);

        grammar.insert("B", vec![
            vec![RuleElement::Terminal('c')],
        ]);

        let first_set  = get_first_set(&grammar).unwrap();
        let follow_set = get_follow_set(&grammar, &first_set);

        let mut start_parse = BTreeMap::new();
        start_parse.insert('c', vec![RuleElement::NonTerminal("A")]);

        let mut a_parse = BTreeMap::new();
        a_parse.insert('c', vec![
            RuleElement::Empty,
            RuleElement::NonTerminal("B"),
        ]);

        let mut b_parse = BTreeMap::new();
        b_parse.insert('c', vec![RuleElement::Terminal('c')]);

        let mut expected_parse_table = BTreeMap::new();
        expected_parse_table.insert("START", start_parse);
        expected_parse_table.insert("A",     a_parse);
        expected_parse_table.insert("B",     b_parse);

        assert!(expected_parse_table == get_parse_table(&grammar, &first_set, &follow_set).unwrap());
    }

    #[test]
    fn combo_te_nt_nt() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Terminal('c')],
            vec![RuleElement::Empty],
        ]);

        grammar.insert("B", vec![
            vec![RuleElement::NonTerminal("A"), RuleElement::Terminal('c')],
        ]);

        grammar.insert("C", vec![
            vec![RuleElement::NonTerminal("A"), RuleElement::Terminal('c')],
        ]);

        let first_set  = get_first_set(&grammar).unwrap();
        let follow_set = get_follow_set(&grammar, &first_set);

        match get_parse_table(&grammar, &first_set, &follow_set) {
            Ok(_)    => panic!(),
            Err(err) => assert!(err == GrammarError::Conflict {
                non_terminal: "A",
                rule:         vec![RuleElement::Empty],
                rule_element: RuleElement::Empty,
            }),
        }
    }

    #[test]
    fn combo_ne_nt_nt() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Terminal('c')],
            vec![RuleElement::Empty],
        ]);

        grammar.insert("B", vec![
            vec![RuleElement::NonTerminal("A"), RuleElement::Terminal('c')],
        ]);

        grammar.insert("C", vec![
            vec![RuleElement::NonTerminal("A"), RuleElement::Terminal('c')],
        ]);

        let first_set  = get_first_set(&grammar).unwrap();
        let follow_set = get_follow_set(&grammar, &first_set);

        match get_parse_table(&grammar, &first_set, &follow_set) {
            Ok(_)    => panic!(),
            Err(err) => assert!(err == GrammarError::Conflict {
                non_terminal: "A",
                rule:         vec![RuleElement::Empty],
                rule_element: RuleElement::Empty,
            }),
        }
    }

    #[test]
    fn combo_t() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Terminal('b')],
        ]);

        let first_set  = get_first_set(&grammar).unwrap();
        let follow_set = get_follow_set(&grammar, &first_set);

        let mut start_parse = BTreeMap::new();
        start_parse.insert('b', vec![RuleElement::NonTerminal("A")]);

        let mut a_parse = BTreeMap::new();
        a_parse.insert('b', vec![RuleElement::Terminal('b')]);

        let mut expected_parse_table = BTreeMap::new();
        expected_parse_table.insert("START", start_parse);
        expected_parse_table.insert("A",     a_parse);

        assert!(expected_parse_table == get_parse_table(&grammar, &first_set, &follow_set).unwrap());
    }

    #[test]
    fn combo_te() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Terminal('b'), RuleElement::Empty],
        ]);

        let first_set  = get_first_set(&grammar).unwrap();
        let follow_set = get_follow_set(&grammar, &first_set);

        let mut start_parse = BTreeMap::new();
        start_parse.insert('b', vec![RuleElement::NonTerminal("A")]);

        let mut a_parse = BTreeMap::new();
        a_parse.insert('b', vec![RuleElement::Terminal('b'), RuleElement::Empty]);

        let mut expected_parse_table = BTreeMap::new();
        expected_parse_table.insert("START", start_parse);
        expected_parse_table.insert("A",     a_parse);

        assert!(expected_parse_table == get_parse_table(&grammar, &first_set, &follow_set).unwrap());
    }

    #[test]
    fn combo_tt() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Terminal('b'), RuleElement::Terminal('c')],
        ]);

        let first_set  = get_first_set(&grammar).unwrap();
        let follow_set = get_follow_set(&grammar, &first_set);

        let mut start_parse = BTreeMap::new();
        start_parse.insert('b', vec![RuleElement::NonTerminal("A")]);

        let mut a_parse = BTreeMap::new();
        a_parse.insert('b', vec![RuleElement::Terminal('b'), RuleElement::Terminal('c')]);

        let mut expected_parse_table = BTreeMap::new();
        expected_parse_table.insert("START", start_parse);
        expected_parse_table.insert("A",     a_parse);

        assert!(expected_parse_table == get_parse_table(&grammar, &first_set, &follow_set).unwrap());
    }

    #[test]
    fn combo_t_t() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Terminal('b')],
            vec![RuleElement::Terminal('b')],
        ]);

        let first_set  = get_first_set(&grammar).unwrap();
        let follow_set = get_follow_set(&grammar, &first_set);

        match get_parse_table(&grammar, &first_set, &follow_set) {
            Ok(_)    => panic!(),
            Err(err) => assert!(err == GrammarError::Conflict {
                non_terminal: "A",
                rule:         vec![RuleElement::Terminal('b')],
                rule_element: RuleElement::Terminal('b'),
            }),
        }
    }

    #[test]
    fn combo_t_et() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Terminal('b')],
            vec![RuleElement::Empty, RuleElement::Terminal('b')],
        ]);

        let first_set  = get_first_set(&grammar).unwrap();
        let follow_set = get_follow_set(&grammar, &first_set);

        match get_parse_table(&grammar, &first_set, &follow_set) {
            Ok(_)    => panic!(),
            Err(err) => assert!(err == GrammarError::Conflict {
                non_terminal: "A",
                rule:         vec![RuleElement::Empty, RuleElement::Terminal('b')],
                rule_element: RuleElement::Terminal('b'),
            }),
        }
    }

    #[test]
    fn combo_tn_e() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Terminal('b'), RuleElement::NonTerminal("C")],
        ]);

        grammar.insert("C", vec![
            vec![RuleElement::Empty],
        ]);

        let first_set  = get_first_set(&grammar).unwrap();
        let follow_set = get_follow_set(&grammar, &first_set);

        let mut start_parse = BTreeMap::new();
        start_parse.insert('b', vec![RuleElement::NonTerminal("A")]);

        let mut a_parse = BTreeMap::new();
        a_parse.insert('b', vec![RuleElement::Terminal('b'), RuleElement::NonTerminal("C")]);

        let mut expected_parse_table = BTreeMap::new();
        expected_parse_table.insert("START", start_parse);
        expected_parse_table.insert("A",     a_parse);
        expected_parse_table.insert("C",     BTreeMap::new());

        assert!(expected_parse_table == get_parse_table(&grammar, &first_set, &follow_set).unwrap());
    }

    #[test]
    fn combo_tn_t() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Terminal('b'), RuleElement::NonTerminal("C")],
        ]);

        grammar.insert("C", vec![
            vec![RuleElement::Terminal('d')],
        ]);

        let first_set  = get_first_set(&grammar).unwrap();
        let follow_set = get_follow_set(&grammar, &first_set);

        let mut start_parse = BTreeMap::new();
        start_parse.insert('b', vec![RuleElement::NonTerminal("A")]);

        let mut a_parse = BTreeMap::new();
        a_parse.insert('b', vec![
            RuleElement::Terminal('b'),
            RuleElement::NonTerminal("C"),
        ]);

        let mut c_parse = BTreeMap::new();
        c_parse.insert('d', vec![RuleElement::Terminal('d')]);

        let mut expected_parse_table = BTreeMap::new();
        expected_parse_table.insert("START", start_parse);
        expected_parse_table.insert("A",     a_parse);
        expected_parse_table.insert("C",     c_parse);

        assert!(expected_parse_table == get_parse_table(&grammar, &first_set, &follow_set).unwrap());
    }

    #[test]
    fn combo_n_e() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::NonTerminal("B")],
        ]);

        grammar.insert("B", vec![
            vec![RuleElement::Empty],
        ]);

        let first_set  = get_first_set(&grammar).unwrap();
        let follow_set = get_follow_set(&grammar, &first_set);

        let mut expected_parse_table = BTreeMap::new();
        expected_parse_table.insert("START", BTreeMap::new());
        expected_parse_table.insert("A",     BTreeMap::new());
        expected_parse_table.insert("B",     BTreeMap::new());

        assert!(expected_parse_table == get_parse_table(&grammar, &first_set, &follow_set).unwrap());
    }

    #[test]
    fn combo_n_t() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::NonTerminal("B")],
        ]);

        grammar.insert("B", vec![
            vec![RuleElement::Terminal('c')],
        ]);

        let first_set  = get_first_set(&grammar).unwrap();
        let follow_set = get_follow_set(&grammar, &first_set);

        let mut start_parse = BTreeMap::new();
        start_parse.insert('c', vec![RuleElement::NonTerminal("A")]);

        let mut a_parse = BTreeMap::new();
        a_parse.insert('c', vec![
            RuleElement::NonTerminal("B"),
        ]);

        let mut b_parse = BTreeMap::new();
        b_parse.insert('c', vec![RuleElement::Terminal('c')]);

        let mut expected_parse_table = BTreeMap::new();
        expected_parse_table.insert("START", start_parse);
        expected_parse_table.insert("A",     a_parse);
        expected_parse_table.insert("B",     b_parse);

        assert!(expected_parse_table == get_parse_table(&grammar, &first_set, &follow_set).unwrap());
    }

    #[test]
    fn combo_ne_e() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::NonTerminal("B"), RuleElement::Empty],
        ]);

        grammar.insert("B", vec![
            vec![RuleElement::Empty],
        ]);

        let first_set  = get_first_set(&grammar).unwrap();
        let follow_set = get_follow_set(&grammar, &first_set);

        let mut expected_parse_table = BTreeMap::new();
        expected_parse_table.insert("START", BTreeMap::new());
        expected_parse_table.insert("A",     BTreeMap::new());
        expected_parse_table.insert("B",     BTreeMap::new());

        assert!(expected_parse_table == get_parse_table(&grammar, &first_set, &follow_set).unwrap());
    }

    #[test]
    fn combo_ne_t() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::NonTerminal("B"), RuleElement::Empty],
        ]);

        grammar.insert("B", vec![
            vec![RuleElement::Terminal('c')],
        ]);

        let first_set  = get_first_set(&grammar).unwrap();
        let follow_set = get_follow_set(&grammar, &first_set);

        let mut start_parse = BTreeMap::new();
        start_parse.insert('c', vec![RuleElement::NonTerminal("A")]);

        let mut a_parse = BTreeMap::new();
        a_parse.insert('c', vec![
            RuleElement::NonTerminal("B"),
            RuleElement::Empty,
        ]);

        let mut b_parse = BTreeMap::new();
        b_parse.insert('c', vec![RuleElement::Terminal('c')]);

        let mut expected_parse_table = BTreeMap::new();
        expected_parse_table.insert("START", start_parse);
        expected_parse_table.insert("A",     a_parse);
        expected_parse_table.insert("B",     b_parse);

        assert!(expected_parse_table == get_parse_table(&grammar, &first_set, &follow_set).unwrap());
    }

    #[test]
    fn combo_ne_t_nt() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::NonTerminal("B")],
            vec![RuleElement::Empty],
        ]);

        grammar.insert("B", vec![
            vec![RuleElement::Terminal('c')],
        ]);

        grammar.insert("C", vec![
            vec![RuleElement::NonTerminal("A"), RuleElement::Terminal('c')],
        ]);

        let first_set  = get_first_set(&grammar).unwrap();
        let follow_set = get_follow_set(&grammar, &first_set);

        match get_parse_table(&grammar, &first_set, &follow_set) {
            Ok(_)    => panic!(),
            Err(err) => assert!(err == GrammarError::Conflict {
                non_terminal: "A",
                rule:         vec![RuleElement::Empty],
                rule_element: RuleElement::Empty,
            }),
        }
    }

    #[test]
    fn combo_nt_e() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::NonTerminal("B"), RuleElement::Terminal('c')],
        ]);

        grammar.insert("B", vec![
            vec![RuleElement::Empty],
        ]);

        let first_set  = get_first_set(&grammar).unwrap();
        let follow_set = get_follow_set(&grammar, &first_set);

        let mut start_parse = BTreeMap::new();
        start_parse.insert('c', vec![RuleElement::NonTerminal("A")]);

        let mut a_parse = BTreeMap::new();
        a_parse.insert('c', vec![
            RuleElement::NonTerminal("B"),
            RuleElement::Terminal('c'),
        ]);

        let mut b_parse = BTreeMap::new();
        b_parse.insert('c', vec![RuleElement::Empty]);

        let mut expected_parse_table = BTreeMap::new();
        expected_parse_table.insert("START", start_parse);
        expected_parse_table.insert("A",     a_parse);
        expected_parse_table.insert("B",     b_parse);

        assert!(expected_parse_table == get_parse_table(&grammar, &first_set, &follow_set).unwrap());
    }

    #[test]
    fn combo_nt_t() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::NonTerminal("B"), RuleElement::Terminal('c')],
        ]);

        grammar.insert("B", vec![
            vec![RuleElement::Terminal('d')],
        ]);

        let first_set  = get_first_set(&grammar).unwrap();
        let follow_set = get_follow_set(&grammar, &first_set);

        let mut start_parse = BTreeMap::new();
        start_parse.insert('d', vec![RuleElement::NonTerminal("A")]);

        let mut a_parse = BTreeMap::new();
        a_parse.insert('d', vec![
            RuleElement::NonTerminal("B"),
            RuleElement::Terminal('c'),
        ]);

        let mut b_parse = BTreeMap::new();
        b_parse.insert('d', vec![RuleElement::Terminal('d')]);

        let mut expected_parse_table = BTreeMap::new();
        expected_parse_table.insert("START", start_parse);
        expected_parse_table.insert("A",     a_parse);
        expected_parse_table.insert("B",     b_parse);

        assert!(expected_parse_table == get_parse_table(&grammar, &first_set, &follow_set).unwrap());
    }

    #[test]
    fn combo_nn_e() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::NonTerminal("B"), RuleElement::NonTerminal("C")],
        ]);

        grammar.insert("B", vec![
            vec![RuleElement::Empty],
        ]);

        grammar.insert("C", vec![
            vec![RuleElement::Empty],
        ]);

        let first_set  = get_first_set(&grammar).unwrap();
        let follow_set = get_follow_set(&grammar, &first_set);

        let mut expected_parse_table = BTreeMap::new();
        expected_parse_table.insert("START", BTreeMap::new());
        expected_parse_table.insert("A",     BTreeMap::new());
        expected_parse_table.insert("B",     BTreeMap::new());
        expected_parse_table.insert("C",     BTreeMap::new());

        assert!(expected_parse_table == get_parse_table(&grammar, &first_set, &follow_set).unwrap());
    }

    #[test]
    fn combo_nn_t() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::NonTerminal("B"), RuleElement::NonTerminal("C")],
        ]);

        grammar.insert("B", vec![
            vec![RuleElement::Empty],
        ]);

        grammar.insert("C", vec![
            vec![RuleElement::Terminal('d')],
        ]);

        let first_set  = get_first_set(&grammar).unwrap();
        let follow_set = get_follow_set(&grammar, &first_set);

        let mut start_parse = BTreeMap::new();
        start_parse.insert('d', vec![RuleElement::NonTerminal("A")]);

        let mut a_parse = BTreeMap::new();
        a_parse.insert('d', vec![
            RuleElement::NonTerminal("B"),
            RuleElement::NonTerminal("C"),
        ]);

        let mut b_parse = BTreeMap::new();
        b_parse.insert('d', vec![RuleElement::Empty]);

        let mut c_parse = BTreeMap::new();
        c_parse.insert('d', vec![
            RuleElement::Terminal('d'),
        ]);

        let mut expected_parse_table = BTreeMap::new();
        expected_parse_table.insert("START", start_parse);
        expected_parse_table.insert("A",     a_parse);
        expected_parse_table.insert("B",     b_parse);
        expected_parse_table.insert("C",     c_parse);

        assert!(expected_parse_table == get_parse_table(&grammar, &first_set, &follow_set).unwrap());
    }

    #[test]
    fn combo_n_n() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::Terminal('b')],
            vec![RuleElement::NonTerminal("C")],
        ]);

        grammar.insert("C", vec![
            vec![RuleElement::Terminal('b')],
        ]);

        let first_set  = get_first_set(&grammar).unwrap();
        let follow_set = get_follow_set(&grammar, &first_set);

        match get_parse_table(&grammar, &first_set, &follow_set) {
            Ok(_)    => panic!(),
            Err(err) => assert!(err == GrammarError::Conflict {
                non_terminal: "A",
                rule:         vec![RuleElement::NonTerminal("C")],
                rule_element: RuleElement::NonTerminal("C"),
            }),
        }
    }

    #[test]
    fn combo_nn_t_t() {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("A")],
        ]);

        grammar.insert("A", vec![
            vec![RuleElement::NonTerminal("B")],
            vec![RuleElement::NonTerminal("C")],
        ]);

        grammar.insert("B", vec![
            vec![RuleElement::Terminal('b')],
        ]);

        grammar.insert("C", vec![
            vec![RuleElement::Terminal('b')],
        ]);

        let first_set  = get_first_set(&grammar).unwrap();
        let follow_set = get_follow_set(&grammar, &first_set);

        match get_parse_table(&grammar, &first_set, &follow_set) {
            Ok(_)    => panic!(),
            Err(err) => assert!(err == GrammarError::Conflict {
                non_terminal: "A",
                rule:         vec![RuleElement::NonTerminal("C")],
                rule_element: RuleElement::NonTerminal("C"),
            }),
        }
    }
}

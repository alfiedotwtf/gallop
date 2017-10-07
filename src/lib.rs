use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::iter::Peekable;
use std::str::Chars;
use std::char;

// TODO: need utilities like STRING

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
    ReservedNonTerminal(NonTerminal<'a>),
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
    pub fn new(grammar: &'a mut Grammar) -> Result<Parser<'a>, GrammarError<'a>> {
        match grammar.contains_key("START") {
            false => Err(GrammarError::NoStartSymbol),
            true  => match grammar.len() > 1 {
                false => Err(GrammarError::EmptyGrammar),
                true  => {
                    let reserved_non_terminals          = get_reserved_non_terminals();
                    let mut reserved_non_terminals_used = BTreeSet::new();

                    for (non_terminal, rules) in grammar.iter() {
                        if reserved_non_terminals.contains_key(non_terminal) {
                            return Err(GrammarError::ReservedNonTerminal(non_terminal));
                        }

                        for rule in rules {
                            for rule_element in rule {
                                match *rule_element {
                                    RuleElement::Terminal(_)    => {},
                                    RuleElement::Empty          => {},
                                    RuleElement::NonTerminal(u) => {
                                        if reserved_non_terminals.contains_key(u) {
                                            reserved_non_terminals_used.insert(u);
                                        }
                                    },
                                }
                            }
                        }
                    }

                    for reserved_non_terminal_used in reserved_non_terminals_used {
                        grammar.insert(
                            reserved_non_terminal_used,
                            reserved_non_terminals.get(reserved_non_terminal_used).unwrap().clone(),
                        );
                    }

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
                    None             => {
                        match self.parse_table.get(symbol).unwrap().get(&ParseTableElement::Empty) {
                            Some(empty) => empty,
                            None        => return Some(ParseError::NoMoreInput),
                        }
                    },
                    Some(next_input) => match self.parse_table.get(symbol).unwrap().get(&ParseTableElement::Terminal(*next_input)) {
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

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum ParseTableElement {
    Empty,
    Terminal(char),
}

type ParseTable<'a> = BTreeMap<NonTerminal<'a>, BTreeMap<ParseTableElement, Rule<'a>>>;

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
                        match parse_table_non_terminal.insert(ParseTableElement::Terminal(u), rule.clone()).is_some() {
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
                                    match parse_table_non_terminal.insert(ParseTableElement::Terminal(fu), rule.clone()).is_some() {
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
                        match parse_table_non_terminal.insert(ParseTableElement::Terminal(*follow_u), rule.clone()).is_some() {
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

            let first_non_terminal = first_set.get(non_terminal).unwrap();

            if first_non_terminal.contains(&FirstElement::Empty) {
                parse_table_non_terminal.insert(ParseTableElement::Empty, vec![RuleElement::Empty]);
            }
        }
    }

    Ok(parse_table)
}

fn get_reserved_non_terminals<'a>() -> BTreeMap<NonTerminal<'a>, Vec<Rule<'a>>>{
    let mut reserved_non_terminals = BTreeMap::new();

    reserved_non_terminals.insert("ASCII",                    get_reserved_ascii());
    reserved_non_terminals.insert("ASCII-CONTROL",            get_reserved_ascii_control());
    reserved_non_terminals.insert("ASCII-WHITESPACE",         get_reserved_ascii_whitespace());
    reserved_non_terminals.insert("ASCII-DIGIT",              get_reserved_ascii_digit());
    reserved_non_terminals.insert("ASCII-LOWERCASE",          get_reserved_ascii_lowercase());
    reserved_non_terminals.insert("ASCII-UPPERCASE",          get_reserved_ascii_uppercase());
    reserved_non_terminals.insert("ASCII-ALPHABETIC",         get_reserved_ascii_alphabetic());
    reserved_non_terminals.insert("ASCII-ALPHANUMERIC",       get_reserved_ascii_alphanumeric());
    reserved_non_terminals.insert("ASCII-HEXDIGIT-LOWERCASE", get_reserved_ascii_hexdigit_lowercase());
    reserved_non_terminals.insert("ASCII-HEXDIGIT-UPPERCASE", get_reserved_ascii_hexdigit_uppercase());
    reserved_non_terminals.insert("ASCII-HEXDIGIT",           get_reserved_ascii_hexdigit());
    reserved_non_terminals.insert("CONTROL",                  get_reserved_control());
    reserved_non_terminals.insert("WHITESPACE",               get_reserved_whitespace());
    reserved_non_terminals.insert("NUMERIC",                  get_reserved_numeric());
    reserved_non_terminals.insert("LOWERCASE",                get_reserved_lowercase());
    reserved_non_terminals.insert("UPPERCASE",                get_reserved_uppercase());
    reserved_non_terminals.insert("ALPHABETIC",               get_reserved_alphabetic());
    reserved_non_terminals.insert("ALPHANUMERIC",             get_reserved_alphanumeric());

    reserved_non_terminals
}

fn get_reserved_ascii<'a>() -> Vec<Vec<RuleElement<'a>>> {
    (0x0..(0x7f + 1 as u8))
        .into_iter()
        .map(|c| vec![RuleElement::Terminal(c as char)])
        .collect()
}

fn get_reserved_ascii_control<'a>() -> Vec<Vec<RuleElement<'a>>> {
    let mut characters: Vec<Vec<RuleElement<'a>>> = (0x0..(0x1f + 1 as u8))
        .into_iter()
        .map(|c| vec![RuleElement::Terminal(c as char)])
        .collect();

    characters.push(vec![RuleElement::Terminal(0x7f as char)]);

    characters
}

fn get_reserved_ascii_whitespace<'a>() -> Vec<Vec<RuleElement<'a>>> {
    ['\u{0020}', '\u{0009}','\u{000a}','\u{000c}','\u{000d}']
        .into_iter()
        .map(|c| vec![RuleElement::Terminal(*c)])
        .collect()
}

fn get_reserved_ascii_digit<'a>() -> Vec<Vec<RuleElement<'a>>> {
    (('0' as u8)..('9' as u8 + 1))
        .into_iter()
        .map(|c| vec![RuleElement::Terminal(c as char)])
        .collect()
}

fn get_reserved_ascii_lowercase<'a>() -> Vec<Vec<RuleElement<'a>>> {
    (('a' as u8)..('z' as u8 + 1))
        .into_iter()
        .map(|c| vec![RuleElement::Terminal(c as char)])
        .collect()
}

fn get_reserved_ascii_uppercase<'a>() -> Vec<Vec<RuleElement<'a>>> {
    (('A' as u8)..('Z' as u8 + 1))
        .into_iter()
        .map(|c| vec![RuleElement::Terminal(c as char)])
        .collect()
}

fn get_reserved_ascii_alphabetic<'a>() -> Vec<Vec<RuleElement<'a>>> {
    let mut characters = vec![];

    characters.append(&mut get_reserved_ascii_lowercase().clone());
    characters.append(&mut get_reserved_ascii_uppercase().clone());

    characters
}


fn get_reserved_ascii_alphanumeric<'a>() -> Vec<Vec<RuleElement<'a>>> {
    let mut characters: Vec<Vec<RuleElement>> = Vec::new();

    characters.append(&mut get_reserved_ascii_alphabetic().clone());
    characters.append(&mut get_reserved_ascii_digit().clone());

    characters
}

fn get_reserved_ascii_hexdigit_lowercase<'a>() -> Vec<Vec<RuleElement<'a>>> {
    let mut characters: Vec<Vec<RuleElement<'a>>> = (('a' as u8)..('f' as u8 + 1))
        .into_iter()
        .map(|c| vec![RuleElement::Terminal(c as char)])
        .collect();

    characters.append(&mut get_reserved_ascii_digit().clone());

    characters
}

fn get_reserved_ascii_hexdigit_uppercase<'a>() -> Vec<Vec<RuleElement<'a>>> {
    let mut characters: Vec<Vec<RuleElement<'a>>> = (('A' as u8)..('F' as u8 + 1))
        .into_iter()
        .map(|c| vec![RuleElement::Terminal(c as char)])
        .collect();

    characters.append(&mut get_reserved_ascii_digit().clone());

    characters
}

fn get_reserved_ascii_hexdigit<'a>() -> Vec<Vec<RuleElement<'a>>> {
    let mut characters: Vec<Vec<RuleElement>> = Vec::new();

    characters.append(&mut get_reserved_ascii_hexdigit_lowercase().clone());
    characters.append(&mut get_reserved_ascii_hexdigit_uppercase().clone());
    characters.append(&mut get_reserved_ascii_digit().clone());

    characters
}

fn get_reserved_control<'a>() -> Vec<Vec<RuleElement<'a>>> {
    (0x0..(0x10FFFF + 1))
        .into_iter()
        .filter_map(|c| char::from_u32(c))
        .filter(|c| (*c).is_control())
        .map(|c| vec![RuleElement::Terminal(c as char)])
        .collect()
}

fn get_reserved_whitespace<'a>() -> Vec<Vec<RuleElement<'a>>> {
    (0x0..(0x10FFFF + 1))
        .into_iter()
        .filter_map(|c| char::from_u32(c))
        .filter(|c| (*c).is_whitespace())
        .map(|c| vec![RuleElement::Terminal(c as char)])
        .collect()
}

fn get_reserved_numeric<'a>() -> Vec<Vec<RuleElement<'a>>> {
    (0x0..(0x10FFFF + 1))
        .into_iter()
        .filter_map(|c| char::from_u32(c))
        .filter(|c| (*c).is_numeric())
        .map(|c| vec![RuleElement::Terminal(c as char)])
        .collect()
}

fn get_reserved_lowercase<'a>() -> Vec<Vec<RuleElement<'a>>> {
    (0x0..(0x10FFFF + 1))
        .into_iter()
        .filter_map(|c| char::from_u32(c))
        .filter(|c| (*c).is_lowercase())
        .map(|c| vec![RuleElement::Terminal(c as char)])
        .collect()
}

fn get_reserved_uppercase<'a>() -> Vec<Vec<RuleElement<'a>>> {
    (0x0..(0x10FFFF + 1))
        .into_iter()
        .filter_map(|c| char::from_u32(c))
        .filter(|c| (*c).is_uppercase())
        .map(|c| vec![RuleElement::Terminal(c as char)])
        .collect()
}

fn get_reserved_alphabetic<'a>() -> Vec<Vec<RuleElement<'a>>> {
    let mut characters: Vec<Vec<RuleElement>> = Vec::new();

    characters.append(&mut get_reserved_lowercase().clone());
    characters.append(&mut get_reserved_uppercase().clone());

    characters
}

fn get_reserved_alphanumeric<'a>() -> Vec<Vec<RuleElement<'a>>> {
    let mut characters: Vec<Vec<RuleElement>> = Vec::new();

    characters.append(&mut get_reserved_alphabetic().clone());
    characters.append(&mut get_reserved_numeric().clone());

    characters
}

#[cfg(test)]
mod new {
    use super::*;

    #[test]
    fn no_start_symbol() {
        let mut grammar = Grammar::new();

        match Parser::new(&mut grammar) {
            Ok(_)    => panic!(),
            Err(err) => assert!(err == GrammarError::NoStartSymbol),
        }
    }

    #[test]
    fn empty_grammar() {
        let mut grammar = Grammar::new();
        grammar.insert("START", vec![]);

        match Parser::new(&mut grammar) {
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

        match Parser::new(&mut grammar) {
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

        match Parser::new(&mut grammar) {
            Err(_)     => panic!(),
            Ok(parser) => {
                let mut start_rules = BTreeMap::new();
                start_rules.insert(ParseTableElement::Terminal('a'), vec![RuleElement::NonTerminal("A")]);

                let mut a_rules = BTreeMap::new();
                a_rules.insert(ParseTableElement::Terminal('a'), vec![RuleElement::Terminal('a'), RuleElement::Terminal('b')]);

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

        let mut parser = Parser::new(&mut grammar).unwrap();

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

        let mut parser = Parser::new(&mut grammar).unwrap();

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

        let mut parser = Parser::new(&mut grammar).unwrap();

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
        start_rules.insert(ParseTableElement::Terminal('a'), vec![RuleElement::Terminal('b')]);

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

        let mut parser = Parser::new(&mut grammar).unwrap();

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

        let mut parser = Parser::new(&mut grammar).unwrap();

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

        let mut parser = Parser::new(&mut grammar).unwrap();

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

        let mut parser = Parser::new(&mut grammar).unwrap();

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

        let mut parser = Parser::new(&mut grammar).unwrap();

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

        let mut parser = Parser::new(&mut grammar).unwrap();

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

        let mut a_parse = BTreeMap::new();
        a_parse.insert(ParseTableElement::Empty, vec![RuleElement::Empty]);

        let mut expected_parse_table = BTreeMap::new();
        expected_parse_table.insert("START", BTreeMap::new());
        expected_parse_table.insert("A",     a_parse);

        assert!(expected_parse_table == get_parse_table(&mut grammar, &first_set, &follow_set).unwrap());
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

        assert!(expected_parse_table == get_parse_table(&mut grammar, &first_set, &follow_set).unwrap());
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
        start_parse.insert(ParseTableElement::Terminal('b'), vec![RuleElement::NonTerminal("A")]);

        let mut a_parse = BTreeMap::new();
        a_parse.insert(ParseTableElement::Terminal('b'), vec![RuleElement::Empty, RuleElement::Terminal('b')]);

        let mut expected_parse_table = BTreeMap::new();
        expected_parse_table.insert("START", start_parse);
        expected_parse_table.insert("A",     a_parse);

        assert!(expected_parse_table == get_parse_table(&mut grammar, &first_set, &follow_set).unwrap());
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

        let mut b_parse = BTreeMap::new();
        b_parse.insert(ParseTableElement::Empty, vec![RuleElement::Empty]);

        let mut expected_parse_table = BTreeMap::new();
        expected_parse_table.insert("START", BTreeMap::new());
        expected_parse_table.insert("A",     BTreeMap::new());
        expected_parse_table.insert("B",     b_parse);

        assert!(expected_parse_table == get_parse_table(&mut grammar, &first_set, &follow_set).unwrap());
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
        start_parse.insert(ParseTableElement::Terminal('c'), vec![RuleElement::NonTerminal("A")]);

        let mut a_parse = BTreeMap::new();
        a_parse.insert(ParseTableElement::Terminal('c'), vec![
            RuleElement::Empty,
            RuleElement::NonTerminal("B"),
        ]);

        let mut b_parse = BTreeMap::new();
        b_parse.insert(ParseTableElement::Terminal('c'), vec![RuleElement::Terminal('c')]);

        let mut expected_parse_table = BTreeMap::new();
        expected_parse_table.insert("START", start_parse);
        expected_parse_table.insert("A",     a_parse);
        expected_parse_table.insert("B",     b_parse);

        assert!(expected_parse_table == get_parse_table(&mut grammar, &first_set, &follow_set).unwrap());
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

        match get_parse_table(&mut grammar, &first_set, &follow_set) {
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

        match get_parse_table(&mut grammar, &first_set, &follow_set) {
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
        start_parse.insert(ParseTableElement::Terminal('b'), vec![RuleElement::NonTerminal("A")]);

        let mut a_parse = BTreeMap::new();
        a_parse.insert(ParseTableElement::Terminal('b'), vec![RuleElement::Terminal('b')]);

        let mut expected_parse_table = BTreeMap::new();
        expected_parse_table.insert("START", start_parse);
        expected_parse_table.insert("A",     a_parse);

        assert!(expected_parse_table == get_parse_table(&mut grammar, &first_set, &follow_set).unwrap());
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
        start_parse.insert(ParseTableElement::Terminal('b'), vec![RuleElement::NonTerminal("A")]);

        let mut a_parse = BTreeMap::new();
        a_parse.insert(ParseTableElement::Terminal('b'), vec![RuleElement::Terminal('b'), RuleElement::Empty]);

        let mut expected_parse_table = BTreeMap::new();
        expected_parse_table.insert("START", start_parse);
        expected_parse_table.insert("A",     a_parse);

        assert!(expected_parse_table == get_parse_table(&mut grammar, &first_set, &follow_set).unwrap());
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
        start_parse.insert(ParseTableElement::Terminal('b'), vec![RuleElement::NonTerminal("A")]);

        let mut a_parse = BTreeMap::new();
        a_parse.insert(ParseTableElement::Terminal('b'), vec![RuleElement::Terminal('b'), RuleElement::Terminal('c')]);

        let mut expected_parse_table = BTreeMap::new();
        expected_parse_table.insert("START", start_parse);
        expected_parse_table.insert("A",     a_parse);

        assert!(expected_parse_table == get_parse_table(&mut grammar, &first_set, &follow_set).unwrap());
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

        match get_parse_table(&mut grammar, &first_set, &follow_set) {
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

        match get_parse_table(&mut grammar, &first_set, &follow_set) {
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
        start_parse.insert(ParseTableElement::Terminal('b'), vec![RuleElement::NonTerminal("A")]);

        let mut a_parse = BTreeMap::new();
        a_parse.insert(ParseTableElement::Terminal('b'), vec![RuleElement::Terminal('b'), RuleElement::NonTerminal("C")]);

        let mut c_parse = BTreeMap::new();
        c_parse.insert(ParseTableElement::Empty, vec![RuleElement::Empty]);

        let mut expected_parse_table = BTreeMap::new();
        expected_parse_table.insert("START", start_parse);
        expected_parse_table.insert("A",     a_parse);
        expected_parse_table.insert("C",     c_parse);

        assert!(expected_parse_table == get_parse_table(&mut grammar, &first_set, &follow_set).unwrap());
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
        start_parse.insert(ParseTableElement::Terminal('b'), vec![RuleElement::NonTerminal("A")]);

        let mut a_parse = BTreeMap::new();
        a_parse.insert(ParseTableElement::Terminal('b'), vec![
            RuleElement::Terminal('b'),
            RuleElement::NonTerminal("C"),
        ]);

        let mut c_parse = BTreeMap::new();
        c_parse.insert(ParseTableElement::Terminal('d'), vec![RuleElement::Terminal('d')]);

        let mut expected_parse_table = BTreeMap::new();
        expected_parse_table.insert("START", start_parse);
        expected_parse_table.insert("A",     a_parse);
        expected_parse_table.insert("C",     c_parse);

        assert!(expected_parse_table == get_parse_table(&mut grammar, &first_set, &follow_set).unwrap());
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

        let mut b_parse = BTreeMap::new();
        b_parse.insert(ParseTableElement::Empty, vec![RuleElement::Empty]);

        let mut expected_parse_table = BTreeMap::new();
        expected_parse_table.insert("START", BTreeMap::new());
        expected_parse_table.insert("A",     BTreeMap::new());
        expected_parse_table.insert("B",     b_parse);

        assert!(expected_parse_table == get_parse_table(&mut grammar, &first_set, &follow_set).unwrap());
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
        start_parse.insert(ParseTableElement::Terminal('c'), vec![RuleElement::NonTerminal("A")]);

        let mut a_parse = BTreeMap::new();
        a_parse.insert(ParseTableElement::Terminal('c'), vec![
            RuleElement::NonTerminal("B"),
        ]);

        let mut b_parse = BTreeMap::new();
        b_parse.insert(ParseTableElement::Terminal('c'), vec![RuleElement::Terminal('c')]);

        let mut expected_parse_table = BTreeMap::new();
        expected_parse_table.insert("START", start_parse);
        expected_parse_table.insert("A",     a_parse);
        expected_parse_table.insert("B",     b_parse);

        assert!(expected_parse_table == get_parse_table(&mut grammar, &first_set, &follow_set).unwrap());
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

        let mut b_parse = BTreeMap::new();
        b_parse.insert(ParseTableElement::Empty, vec![RuleElement::Empty]);

        let mut expected_parse_table = BTreeMap::new();
        expected_parse_table.insert("START", BTreeMap::new());
        expected_parse_table.insert("A",     BTreeMap::new());
        expected_parse_table.insert("B",     b_parse);

        assert!(expected_parse_table == get_parse_table(&mut grammar, &first_set, &follow_set).unwrap());
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
        start_parse.insert(ParseTableElement::Terminal('c'), vec![RuleElement::NonTerminal("A")]);

        let mut a_parse = BTreeMap::new();
        a_parse.insert(ParseTableElement::Terminal('c'), vec![
            RuleElement::NonTerminal("B"),
            RuleElement::Empty,
        ]);

        let mut b_parse = BTreeMap::new();
        b_parse.insert(ParseTableElement::Terminal('c'), vec![RuleElement::Terminal('c')]);

        let mut expected_parse_table = BTreeMap::new();
        expected_parse_table.insert("START", start_parse);
        expected_parse_table.insert("A",     a_parse);
        expected_parse_table.insert("B",     b_parse);

        assert!(expected_parse_table == get_parse_table(&mut grammar, &first_set, &follow_set).unwrap());
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

        match get_parse_table(&mut grammar, &first_set, &follow_set) {
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
        start_parse.insert(ParseTableElement::Terminal('c'), vec![RuleElement::NonTerminal("A")]);

        let mut a_parse = BTreeMap::new();
        a_parse.insert(ParseTableElement::Terminal('c'), vec![
            RuleElement::NonTerminal("B"),
            RuleElement::Terminal('c'),
        ]);

        let mut b_parse = BTreeMap::new();
        b_parse.insert(ParseTableElement::Empty, vec![RuleElement::Empty]);
        b_parse.insert(ParseTableElement::Terminal('c'), vec![RuleElement::Empty]);

        let mut expected_parse_table = BTreeMap::new();
        expected_parse_table.insert("START", start_parse);
        expected_parse_table.insert("A",     a_parse);
        expected_parse_table.insert("B",     b_parse);

        assert!(expected_parse_table == get_parse_table(&mut grammar, &first_set, &follow_set).unwrap());
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
        start_parse.insert(ParseTableElement::Terminal('d'), vec![RuleElement::NonTerminal("A")]);

        let mut a_parse = BTreeMap::new();
        a_parse.insert(ParseTableElement::Terminal('d'), vec![
            RuleElement::NonTerminal("B"),
            RuleElement::Terminal('c'),
        ]);

        let mut b_parse = BTreeMap::new();
        b_parse.insert(ParseTableElement::Terminal('d'), vec![RuleElement::Terminal('d')]);

        let mut expected_parse_table = BTreeMap::new();
        expected_parse_table.insert("START", start_parse);
        expected_parse_table.insert("A",     a_parse);
        expected_parse_table.insert("B",     b_parse);

        assert!(expected_parse_table == get_parse_table(&mut grammar, &first_set, &follow_set).unwrap());
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

        let mut b_parse = BTreeMap::new();
        b_parse.insert(ParseTableElement::Empty, vec![RuleElement::Empty]);

        let mut c_parse = BTreeMap::new();
        c_parse.insert(ParseTableElement::Empty, vec![RuleElement::Empty]);

        let mut expected_parse_table = BTreeMap::new();
        expected_parse_table.insert("START", BTreeMap::new());
        expected_parse_table.insert("A",     BTreeMap::new());
        expected_parse_table.insert("B",     b_parse);
        expected_parse_table.insert("C",     c_parse);

        assert!(expected_parse_table == get_parse_table(&mut grammar, &first_set, &follow_set).unwrap());
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
        start_parse.insert(ParseTableElement::Terminal('d'), vec![RuleElement::NonTerminal("A")]);

        let mut a_parse = BTreeMap::new();
        a_parse.insert(ParseTableElement::Terminal('d'), vec![
            RuleElement::NonTerminal("B"),
            RuleElement::NonTerminal("C"),
        ]);

        let mut b_parse = BTreeMap::new();
        b_parse.insert(ParseTableElement::Empty, vec![RuleElement::Empty]);
        b_parse.insert(ParseTableElement::Terminal('d'), vec![RuleElement::Empty]);

        let mut c_parse = BTreeMap::new();
        c_parse.insert(ParseTableElement::Terminal('d'), vec![
            RuleElement::Terminal('d'),
        ]);

        let mut expected_parse_table = BTreeMap::new();
        expected_parse_table.insert("START", start_parse);
        expected_parse_table.insert("A",     a_parse);
        expected_parse_table.insert("B",     b_parse);
        expected_parse_table.insert("C",     c_parse);

        assert!(expected_parse_table == get_parse_table(&mut grammar, &first_set, &follow_set).unwrap());
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

        match get_parse_table(&mut grammar, &first_set, &follow_set) {
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

        match get_parse_table(&mut grammar, &first_set, &follow_set) {
            Ok(_)    => panic!(),
            Err(err) => assert!(err == GrammarError::Conflict {
                non_terminal: "A",
                rule:         vec![RuleElement::NonTerminal("C")],
                rule_element: RuleElement::NonTerminal("C"),
            }),
        }
    }
}

#[cfg(test)]
mod parsing_techniques_2nd_ed {
    use super::*;

    fn get_grammar<'a>() -> Grammar<'a> {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("Session")],
        ]);

        grammar.insert("Session", vec![
            vec![RuleElement::NonTerminal("Facts"), RuleElement::NonTerminal("Question")],
            vec![
                RuleElement::Terminal('('),
                RuleElement::NonTerminal("Session"),
                RuleElement::Terminal(')'),
                RuleElement::NonTerminal("Session"),
            ],
        ]);

        grammar.insert("Facts", vec![
            vec![
                RuleElement::NonTerminal("Fact"),
                RuleElement::NonTerminal("Facts"),
            ],
            vec![RuleElement::Empty],
        ]);

        grammar.insert("Fact", vec![
            vec![
                RuleElement::Terminal('!'),
                RuleElement::NonTerminal("STRING"),
            ]
        ]);

        grammar.insert("Question", vec![
            vec![
                RuleElement::Terminal('?'),
                RuleElement::NonTerminal("STRING"),
            ]
        ]);

        grammar.insert("STRING", vec![
            vec![
                RuleElement::Terminal('x'),
            ],
        ]);

        grammar
    }

    #[test]
    fn pg_243() {
        let grammar = get_grammar();

        let mut expected_first_set = BTreeMap::new();

        let mut start_first = BTreeSet::new();
        start_first.insert(FirstElement::Terminal('('));
        start_first.insert(FirstElement::Terminal('?'));
        start_first.insert(FirstElement::Terminal('!'));

        let mut session_first = BTreeSet::new();
        session_first.insert(FirstElement::Terminal('('));
        session_first.insert(FirstElement::Terminal('?'));
        session_first.insert(FirstElement::Terminal('!'));

        let mut facts_first = BTreeSet::new();
        facts_first.insert(FirstElement::Empty);
        facts_first.insert(FirstElement::Terminal('!'));

        let mut fact_first = BTreeSet::new();
        fact_first.insert(FirstElement::Terminal('!'));

        let mut question_first = BTreeSet::new();
        question_first.insert(FirstElement::Terminal('?'));

        let mut string_first = BTreeSet::new();
        string_first.insert(FirstElement::Terminal('x'));

        expected_first_set.insert("START",    start_first);
        expected_first_set.insert("Session",  session_first);
        expected_first_set.insert("Facts",    facts_first);
        expected_first_set.insert("Fact",     fact_first);
        expected_first_set.insert("Question", question_first);
        expected_first_set.insert("STRING",   string_first);

        assert!(get_first_set(&grammar).unwrap() == expected_first_set);
    }

    #[test]
    fn pg_246() {
        let grammar   = get_grammar();
        let first_set = get_first_set(&grammar).unwrap();

        let mut expected_follow_set: FollowSet = BTreeMap::new();

        let mut session_first = BTreeSet::new();
        session_first.insert(')');

        let mut facts_first = BTreeSet::new();
        facts_first.insert('?');

        let mut fact_first = BTreeSet::new();
        fact_first.insert('!');
        fact_first.insert('?');

        let mut question_first = BTreeSet::new();
        question_first.insert(')');

        let mut string_first = BTreeSet::new();
        string_first.insert('!');

        expected_follow_set.insert("START",    BTreeSet::new());
        expected_follow_set.insert("Session",  session_first);
        expected_follow_set.insert("Facts",    facts_first);
        expected_follow_set.insert("Fact",     fact_first);
        expected_follow_set.insert("Question", question_first);
        expected_follow_set.insert("STRING",   string_first);

        assert!(get_follow_set(&grammar, &first_set) == expected_follow_set);
    }

    #[test]
    fn pg_247() {
        let mut grammar = get_grammar();
        let first_set   = get_first_set(&grammar).unwrap();
        let follow_set  = get_follow_set(&grammar, &first_set);

        let mut expected_parse_table: ParseTable = BTreeMap::new();

        let mut start_parse = BTreeMap::new();
        start_parse.insert(ParseTableElement::Terminal('!'), vec![
          RuleElement::NonTerminal("Session"),
        ]);

        start_parse.insert(ParseTableElement::Terminal('('), vec![
          RuleElement::NonTerminal("Session"),
        ]);

        start_parse.insert(ParseTableElement::Terminal('?'), vec![
          RuleElement::NonTerminal("Session"),
        ]);

        let mut session_parse = BTreeMap::new();

        session_parse.insert(ParseTableElement::Terminal('('), vec![
          RuleElement::Terminal('('),
          RuleElement::NonTerminal("Session"),
          RuleElement::Terminal(')'),
          RuleElement::NonTerminal("Session"),
        ]);

        session_parse.insert(ParseTableElement::Terminal('!'), vec![
          RuleElement::NonTerminal("Facts"),
          RuleElement::NonTerminal("Question"),
        ]);

        session_parse.insert(ParseTableElement::Terminal('?'), vec![
          RuleElement::NonTerminal("Facts"),
          RuleElement::NonTerminal("Question"),
        ]);

        let mut facts_parse = BTreeMap::new();

        facts_parse.insert(ParseTableElement::Terminal('!'), vec![
          RuleElement::NonTerminal("Fact"),
          RuleElement::NonTerminal("Facts"),
        ]);

        facts_parse.insert(ParseTableElement::Terminal('?'), vec![
          RuleElement::Empty,
        ]);

        facts_parse.insert(ParseTableElement::Empty, vec![
          RuleElement::Empty,
        ]);

        let mut fact_parse = BTreeMap::new();

        fact_parse.insert(ParseTableElement::Terminal('!'), vec![
          RuleElement::Terminal('!'),
          RuleElement::NonTerminal("STRING"),
        ]);

        let mut question_parse = BTreeMap::new();

        question_parse.insert(ParseTableElement::Terminal('?'), vec![
          RuleElement::Terminal('?'),
          RuleElement::NonTerminal("STRING"),
        ]);

        let mut string_parse = BTreeMap::new();

        string_parse.insert(ParseTableElement::Terminal('x'), vec![
          RuleElement::Terminal('x'),
        ]);

        expected_parse_table.insert("START",    start_parse);
        expected_parse_table.insert("Session",  session_parse);
        expected_parse_table.insert("Facts",    facts_parse);
        expected_parse_table.insert("Fact",     fact_parse);
        expected_parse_table.insert("Question", question_parse);
        expected_parse_table.insert("STRING",   string_parse);

        assert!(get_parse_table(&mut grammar, &first_set, &follow_set).unwrap() == expected_parse_table);
    }

    #[test]
    fn parse_ok() {
        let mut grammar = get_grammar();
        let mut parser  = Parser::new(&mut grammar).unwrap();

        assert!(parser.parse("!x?x").unwrap() == ParseTree::NonTerminal {
          symbol:   "START",
          children: vec![
            ParseTree::NonTerminal {
              symbol:   "Session",
              children: vec![
                ParseTree::NonTerminal {
                  symbol:   "Facts",
                  children: vec![
                    ParseTree::NonTerminal {
                      symbol:   "Fact",
                      children: vec![
                        ParseTree::Terminal('!'),
                        ParseTree::NonTerminal {
                          symbol:   "STRING",
                          children: vec![
                            ParseTree::Terminal('x'),
                          ],
                        },
                      ],
                    },
                    ParseTree::NonTerminal {
                      symbol:   "Facts",
                      children: vec![],
                    },
                  ],
                },
                ParseTree::NonTerminal {
                  symbol:   "Question",
                  children: vec![
                    ParseTree::Terminal('?'),
                    ParseTree::NonTerminal {
                      symbol:   "STRING",
                      children: vec![
                        ParseTree::Terminal('x'),
                      ],
                    },
                  ],
                },
              ],
            },
          ],
        });
    }
}

#[cfg(test)]
mod compilers_1st_ed {
    use super::*;

    fn get_grammar<'a>() -> Grammar<'a> {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("E")],
        ]);

        grammar.insert("E", vec![
            vec![
                RuleElement::NonTerminal("T"),
                RuleElement::NonTerminal("Edash"),
            ],
        ]);

        grammar.insert("Edash", vec![
            vec![
                RuleElement::Terminal('+'),
                RuleElement::NonTerminal("T"),
                RuleElement::NonTerminal("Edash"),
            ],
            vec![RuleElement::Empty],
        ]);

        grammar.insert("T", vec![
            vec![
                RuleElement::NonTerminal("F"),
                RuleElement::NonTerminal("Tdash"),
            ],
        ]);

        grammar.insert("Tdash", vec![
            vec![
                RuleElement::Terminal('*'),
                RuleElement::NonTerminal("F"),
                RuleElement::NonTerminal("Tdash"),
            ],
            vec![RuleElement::Empty],
        ]);

        grammar.insert("F", vec![
            vec![
                RuleElement::Terminal('('),
                RuleElement::NonTerminal("E"),
                RuleElement::Terminal(')'),
            ],
            vec![
                RuleElement::Terminal('i'),
                RuleElement::Terminal('d'),
            ],
        ]);

        grammar
    }

    #[test]
    fn pg_190() {
        let grammar = get_grammar();

        let mut expected_first_set = BTreeMap::new();

        let mut start_first = BTreeSet::new();
        start_first.insert(FirstElement::Terminal('('));
        start_first.insert(FirstElement::Terminal('i'));

        let mut e_first = BTreeSet::new();
        e_first.insert(FirstElement::Terminal('('));
        e_first.insert(FirstElement::Terminal('i'));

        let mut t_first = BTreeSet::new();
        t_first.insert(FirstElement::Terminal('('));
        t_first.insert(FirstElement::Terminal('i'));

        let mut f_first = BTreeSet::new();
        f_first.insert(FirstElement::Terminal('('));
        f_first.insert(FirstElement::Terminal('i'));

        let mut edash_first = BTreeSet::new();
        edash_first.insert(FirstElement::Terminal('+'));
        edash_first.insert(FirstElement::Empty);

        let mut tdash_first = BTreeSet::new();
        tdash_first.insert(FirstElement::Terminal('*'));
        tdash_first.insert(FirstElement::Empty);

        expected_first_set.insert("START", start_first);
        expected_first_set.insert("E",     e_first);
        expected_first_set.insert("T",     t_first);
        expected_first_set.insert("F",     f_first);
        expected_first_set.insert("Edash", edash_first);
        expected_first_set.insert("Tdash", tdash_first);

        assert!(get_first_set(&grammar).unwrap() == expected_first_set);

        let mut expected_follow_set: FollowSet = BTreeMap::new();

        let mut e_follow = BTreeSet::new();
        e_follow.insert(')');

        let mut edash_follow = BTreeSet::new();
        edash_follow.insert(')');

        let mut t_follow = BTreeSet::new();
        t_follow.insert('+');
        t_follow.insert(')');

        let mut tdash_follow = BTreeSet::new();
        tdash_follow.insert('+');
        tdash_follow.insert(')');

        let mut f_follow = BTreeSet::new();
        f_follow.insert('+');
        f_follow.insert('*');
        f_follow.insert(')');

        expected_follow_set.insert("START", BTreeSet::new());
        expected_follow_set.insert("E",     e_follow);
        expected_follow_set.insert("T",     t_follow);
        expected_follow_set.insert("F",     f_follow);
        expected_follow_set.insert("Edash", edash_follow);
        expected_follow_set.insert("Tdash", tdash_follow);

        assert!(get_follow_set(&grammar, &expected_first_set) == expected_follow_set);
    }

    #[test]
    fn pg_188() {
        let mut grammar = get_grammar();
        let first_set   = get_first_set(&grammar).unwrap();
        let follow_set  = get_follow_set(&grammar, &first_set);

        let mut expected_parse_table: ParseTable = BTreeMap::new();

        let mut start_parse = BTreeMap::new();

        start_parse.insert(ParseTableElement::Terminal('i'), vec![
          RuleElement::NonTerminal("E"),
        ]);

        start_parse.insert(ParseTableElement::Terminal('('), vec![
          RuleElement::NonTerminal("E"),
        ]);

        let mut e_parse = BTreeMap::new();

        e_parse.insert(ParseTableElement::Terminal('i'), vec![
          RuleElement::NonTerminal("T"),
          RuleElement::NonTerminal("Edash"),
        ]);

        e_parse.insert(ParseTableElement::Terminal('('), vec![
          RuleElement::NonTerminal("T"),
          RuleElement::NonTerminal("Edash"),
        ]);

        let mut edash_parse = BTreeMap::new();

        edash_parse.insert(ParseTableElement::Terminal('+'), vec![
          RuleElement::Terminal('+'),
          RuleElement::NonTerminal("T"),
          RuleElement::NonTerminal("Edash"),
        ]);

        edash_parse.insert(ParseTableElement::Terminal(')'), vec![
          RuleElement::Empty,
        ]);

        edash_parse.insert(ParseTableElement::Empty, vec![
          RuleElement::Empty,
        ]);

        let mut t_parse = BTreeMap::new();

        t_parse.insert(ParseTableElement::Terminal('i'), vec![
          RuleElement::NonTerminal("F"),
          RuleElement::NonTerminal("Tdash"),
        ]);

        t_parse.insert(ParseTableElement::Terminal('('), vec![
          RuleElement::NonTerminal("F"),
          RuleElement::NonTerminal("Tdash"),
        ]);

        let mut tdash_parse = BTreeMap::new();

        tdash_parse.insert(ParseTableElement::Terminal('+'), vec![
          RuleElement::Empty,
        ]);

        tdash_parse.insert(ParseTableElement::Terminal('*'), vec![
          RuleElement::Terminal('*'),
          RuleElement::NonTerminal("F"),
          RuleElement::NonTerminal("Tdash"),
        ]);

        tdash_parse.insert(ParseTableElement::Terminal(')'), vec![
          RuleElement::Empty,
        ]);

        tdash_parse.insert(ParseTableElement::Empty, vec![
          RuleElement::Empty,
        ]);

        let mut f_parse = BTreeMap::new();

        f_parse.insert(ParseTableElement::Terminal('i'), vec![
          RuleElement::Terminal('i'),
          RuleElement::Terminal('d'),
        ]);

        f_parse.insert(ParseTableElement::Terminal('('), vec![
          RuleElement::Terminal('('),
          RuleElement::NonTerminal("E"),
          RuleElement::Terminal(')'),
        ]);

        expected_parse_table.insert("START", start_parse);
        expected_parse_table.insert("E",     e_parse);
        expected_parse_table.insert("Edash", edash_parse);
        expected_parse_table.insert("T",     t_parse);
        expected_parse_table.insert("Tdash", tdash_parse);
        expected_parse_table.insert("F",     f_parse);

        assert!(get_parse_table(&mut grammar, &first_set, &follow_set).unwrap() == expected_parse_table);
    }

    #[test]
    fn parse_ok() {
        let mut grammar = get_grammar();
        let mut parser  = Parser::new(&mut grammar).unwrap();

        assert!(parser.parse("id").unwrap() == ParseTree::NonTerminal {
          symbol:   "START",
          children: vec![
            ParseTree::NonTerminal {
              symbol:   "E",
              children: vec![
                ParseTree::NonTerminal {
                  symbol:   "T",
                  children: vec![
                    ParseTree::NonTerminal {
                      symbol:   "F",
                      children: vec![
                        ParseTree::Terminal('i'),
                        ParseTree::Terminal('d'),
                      ],
                    },
                    ParseTree::NonTerminal {
                      symbol:   "Tdash",
                      children: vec![],
                    },
                  ],
                },
                ParseTree::NonTerminal {
                  symbol:   "Edash",
                  children: vec![],
                },
              ],
            },
          ],
        });
    }
}

#[cfg(test)]
mod compiler_design_in_c_1st {
    use super::*;

    fn get_grammar<'a>() -> Grammar<'a> {
        let mut grammar = Grammar::new();

        grammar.insert("START", vec![
            vec![RuleElement::NonTerminal("stmt")],
        ]);

        grammar.insert("stmt", vec![
            vec![
                RuleElement::NonTerminal("expr"),
                RuleElement::Terminal(';'),
            ],
        ]);

        grammar.insert("expr", vec![
            vec![
                RuleElement::NonTerminal("term"),
                RuleElement::NonTerminal("exprdash"),
            ],
            vec![RuleElement::Empty],
        ]);

        grammar.insert("exprdash", vec![
            vec![
                RuleElement::Terminal('+'),
                RuleElement::NonTerminal("term"),
                RuleElement::NonTerminal("exprdash"),
            ],
            vec![RuleElement::Empty],
        ]);

        grammar.insert("term", vec![
            vec![
                RuleElement::NonTerminal("factor"),
                RuleElement::NonTerminal("termdash"),
            ],
        ]);

        grammar.insert("termdash", vec![
            vec![
                RuleElement::Terminal('*'),
                RuleElement::NonTerminal("factor"),
                RuleElement::NonTerminal("termdash"),
            ],
            vec![RuleElement::Empty],
        ]);

        grammar.insert("factor", vec![
            vec![
                RuleElement::Terminal('('),
                RuleElement::NonTerminal("expr"),
                RuleElement::Terminal(')'),
            ],
            vec![
                RuleElement::Terminal('0'),
            ],
        ]);

        grammar
    }

    #[test]
    fn pg_214() {
        let grammar = get_grammar();

        let mut expected_first_set = BTreeMap::new();

        let mut start_first = BTreeSet::new();
        start_first.insert(FirstElement::Terminal('('));
        start_first.insert(FirstElement::Terminal('0'));
        start_first.insert(FirstElement::Terminal(';'));

        let mut stmt_first = BTreeSet::new();
        stmt_first.insert(FirstElement::Terminal('('));
        stmt_first.insert(FirstElement::Terminal('0'));
        stmt_first.insert(FirstElement::Terminal(';'));

        let mut expr_first = BTreeSet::new();
        expr_first.insert(FirstElement::Terminal('('));
        expr_first.insert(FirstElement::Terminal('0'));
        expr_first.insert(FirstElement::Empty);

        let mut exprdash_first = BTreeSet::new();
        exprdash_first.insert(FirstElement::Terminal('+'));
        exprdash_first.insert(FirstElement::Empty);

        let mut term_first = BTreeSet::new();
        term_first.insert(FirstElement::Terminal('('));
        term_first.insert(FirstElement::Terminal('0'));

        let mut termdash_first = BTreeSet::new();
        termdash_first.insert(FirstElement::Terminal('*'));
        termdash_first.insert(FirstElement::Empty);

        let mut factor_first = BTreeSet::new();
        factor_first.insert(FirstElement::Terminal('('));
        factor_first.insert(FirstElement::Terminal('0'));

        expected_first_set.insert("START",    start_first);
        expected_first_set.insert("stmt",     stmt_first);
        expected_first_set.insert("expr",     expr_first);
        expected_first_set.insert("exprdash", exprdash_first);
        expected_first_set.insert("term",     term_first);
        expected_first_set.insert("termdash", termdash_first);
        expected_first_set.insert("factor",   factor_first);

        assert!(get_first_set(&grammar).unwrap() == expected_first_set);
    }

    #[test]
    fn pg_217() {
        let grammar   = get_grammar();
        let first_set = get_first_set(&grammar).unwrap();

        let mut expected_follow_set: FollowSet = BTreeMap::new();

        let mut expr_follow = BTreeSet::new();
        expr_follow.insert(')');
        expr_follow.insert(';');

        let mut exprdash_follow = BTreeSet::new();
        exprdash_follow.insert(')');
        exprdash_follow.insert(';');

        let mut term_follow = BTreeSet::new();
        term_follow.insert('+');
        term_follow.insert(';');
        term_follow.insert(')');

        let mut termdash_follow = BTreeSet::new();
        termdash_follow.insert('+');
        termdash_follow.insert(';');
        termdash_follow.insert(')');

        let mut factor_follow = BTreeSet::new();
        factor_follow.insert('*');
        factor_follow.insert('+');
        factor_follow.insert(';');
        factor_follow.insert(')');

        expected_follow_set.insert("START", BTreeSet::new());
        expected_follow_set.insert("stmt",  BTreeSet::new());
        expected_follow_set.insert("expr",  expr_follow);
        expected_follow_set.insert("exprdash",  exprdash_follow);
        expected_follow_set.insert("term", term_follow);
        expected_follow_set.insert("termdash",  termdash_follow);
        expected_follow_set.insert("factor",  factor_follow);


        assert!(get_follow_set(&grammar, &first_set) == expected_follow_set);
    }

    #[test]
    fn get_parse_table_ok() {
        let mut grammar = get_grammar();
        let first_set   = get_first_set(&grammar).unwrap();
        let follow_set  = get_follow_set(&grammar, &first_set);

        let mut expected_parse_table: ParseTable = BTreeMap::new();

        let mut start_parse = BTreeMap::new();

        start_parse.insert(ParseTableElement::Terminal('('), vec![
          RuleElement::NonTerminal("stmt"),
        ]);

        start_parse.insert(ParseTableElement::Terminal('0'), vec![
          RuleElement::NonTerminal("stmt"),
        ]);

        start_parse.insert(ParseTableElement::Terminal(';'), vec![
          RuleElement::NonTerminal("stmt"),
        ]);

        let mut stmt_parse = BTreeMap::new();

        stmt_parse.insert(ParseTableElement::Terminal('('), vec![
          RuleElement::NonTerminal("expr"),
          RuleElement::Terminal(';'),
        ]);

        stmt_parse.insert(ParseTableElement::Terminal('0'), vec![
          RuleElement::NonTerminal("expr"),
          RuleElement::Terminal(';'),
        ]);

        stmt_parse.insert(ParseTableElement::Terminal(';'), vec![
          RuleElement::NonTerminal("expr"),
          RuleElement::Terminal(';'),
        ]);

        let mut stmt_parse = BTreeMap::new();

        stmt_parse.insert(ParseTableElement::Terminal('('), vec![
          RuleElement::NonTerminal("expr"),
          RuleElement::Terminal(';'),
        ]);

        stmt_parse.insert(ParseTableElement::Terminal('0'), vec![
          RuleElement::NonTerminal("expr"),
          RuleElement::Terminal(';'),
        ]);

        stmt_parse.insert(ParseTableElement::Terminal(';'), vec![
          RuleElement::NonTerminal("expr"),
          RuleElement::Terminal(';'),
        ]);

        let mut expr_parse = BTreeMap::new();

        expr_parse.insert(ParseTableElement::Terminal('('), vec![
          RuleElement::NonTerminal("term"),
          RuleElement::NonTerminal("exprdash"),
        ]);

        expr_parse.insert(ParseTableElement::Terminal('0'), vec![
          RuleElement::NonTerminal("term"),
          RuleElement::NonTerminal("exprdash"),
        ]);

        expr_parse.insert(ParseTableElement::Terminal(')'), vec![
          RuleElement::Empty,
        ]);

        expr_parse.insert(ParseTableElement::Terminal(';'), vec![
          RuleElement::Empty,
        ]);

        expr_parse.insert(ParseTableElement::Empty, vec![
          RuleElement::Empty,
        ]);

        let mut exprdash_parse = BTreeMap::new();

        exprdash_parse.insert(ParseTableElement::Terminal('+'), vec![
          RuleElement::Terminal('+'),
          RuleElement::NonTerminal("term"),
          RuleElement::NonTerminal("exprdash"),
        ]);

        exprdash_parse.insert(ParseTableElement::Terminal(')'), vec![
          RuleElement::Empty,
        ]);

        exprdash_parse.insert(ParseTableElement::Terminal(';'), vec![
          RuleElement::Empty,
        ]);

        exprdash_parse.insert(ParseTableElement::Empty, vec![
          RuleElement::Empty,
        ]);

        let mut term_parse = BTreeMap::new();

        term_parse.insert(ParseTableElement::Terminal('('), vec![
          RuleElement::NonTerminal("factor"),
          RuleElement::NonTerminal("termdash"),
        ]);

        term_parse.insert(ParseTableElement::Terminal('0'), vec![
          RuleElement::NonTerminal("factor"),
          RuleElement::NonTerminal("termdash"),
        ]);

        let mut termdash_parse = BTreeMap::new();

        termdash_parse.insert(ParseTableElement::Terminal(')'), vec![
          RuleElement::Empty,
        ]);

        termdash_parse.insert(ParseTableElement::Empty, vec![
          RuleElement::Empty,
        ]);

        termdash_parse.insert(ParseTableElement::Terminal('*'), vec![
          RuleElement::Terminal('*'),
          RuleElement::NonTerminal("factor"),
          RuleElement::NonTerminal("termdash"),
        ]);

        termdash_parse.insert(ParseTableElement::Terminal('+'), vec![
          RuleElement::Empty,
        ]);

        termdash_parse.insert(ParseTableElement::Terminal(';'), vec![
          RuleElement::Empty,
        ]);

        let mut factor_parse = BTreeMap::new();

        factor_parse.insert(ParseTableElement::Terminal('('), vec![
          RuleElement::Terminal('('),
          RuleElement::NonTerminal("expr"),
          RuleElement::Terminal(')'),
        ]);

        factor_parse.insert(ParseTableElement::Terminal('0'), vec![
          RuleElement::Terminal('0'),
        ]);

        expected_parse_table.insert("START",    start_parse);
        expected_parse_table.insert("stmt",     stmt_parse);
        expected_parse_table.insert("expr",     expr_parse);
        expected_parse_table.insert("exprdash", exprdash_parse);
        expected_parse_table.insert("term",     term_parse);
        expected_parse_table.insert("termdash", termdash_parse);
        expected_parse_table.insert("factor",   factor_parse);

        assert!(get_parse_table(&mut grammar, &first_set, &follow_set).unwrap() == expected_parse_table);
    }

    #[test]
    fn parse_ok() {
        let mut grammar = get_grammar();
        let mut parser  = Parser::new(&mut grammar).unwrap();

        assert!(parser.parse("();").unwrap() == ParseTree::NonTerminal {
          symbol:   "START",
          children: vec![
            ParseTree::NonTerminal {
              symbol:   "stmt",
              children: vec![
                ParseTree::NonTerminal {
                  symbol:   "expr",
                  children: vec![
                    ParseTree::NonTerminal {
                      symbol:   "term",
                      children: vec![
                        ParseTree::NonTerminal {
                          symbol:   "factor",
                          children: vec![
                            ParseTree::Terminal('('),
                            ParseTree::NonTerminal {
                              symbol:   "expr",
                              children: vec![],
                            },
                            ParseTree::Terminal(')'),
                          ],
                        },
                        ParseTree::NonTerminal {
                          symbol:   "termdash",
                          children: vec![
                          ],
                        },
                      ],
                    },
                    ParseTree::NonTerminal {
                      symbol:   "exprdash",
                      children: vec![],
                    },
                  ],
                },
                ParseTree::Terminal(';'),
              ],
            },
          ],
        });
    }
}

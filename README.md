# NAME

gallop - General LL(1) Parser

See the [documentation](https://docs.rs/gallop/) for the tutorial.

## Example

    let mut grammar: Grammar = BTreeMap::new();

    grammar.insert("START", vec![
      vec![RuleElement::NonTerminal("a+")],
    ]);

    grammar.insert("a+", vec![
      vec![RuleElement::Terminal('a'), RuleElement::NonTerminal("a*")],
    ]);

    grammar.insert("a*", vec![
      vec![RuleElement::Terminal('a'), RuleElement::NonTerminal("a*")],
      vec![RuleElement::Empty],
    ]);

    let mut parser = Parser::new(&mut grammar).unwrap();

    assert!(parser.parse("aaa").unwrap() == ParseTree::NonTerminal {
        symbol:   "START",
        children: vec![ParseTree::Terminal('a'), ParseTree::Terminal('a'), ParseTree::Terminal('a')],
    });

# SUPPORT

Please report any bugs or feature requests at:

* [https://github.com/alfiedotwtf/gallop/issues](https://github.com/alfiedotwtf/gallop/issues)

Feel free to fork the repository and submit pull requests :)

# SEE ALSO

* [Compiler Design in C by Holub](https://www.amazon.com/Compiler-Design-C-Prentice-Hall-software/dp/0131550454)
* [Compilers Principles, Techniques and Tools by Aho et al.](https://www.amazon.com/Compilers-Principles-Techniques-Tools-2nd/dp/0321486811)
* [Parsing Techniques - A Practicle Guide by Grune & Jacobs](https://www.amazon.com/Parsing-Techniques-Practical-Monographs-Computer/dp/1441919015)

# AUTHOR

[Alfie John](https://www.alfie.wtf)

# WARRANTY

IT COMES WITHOUT WARRANTY OF ANY KIND.

# COPYRIGHT AND LICENSE

Copyright (C) 2021 by Alfie John

This program is free software: you can redistribute it and/or modify it under
the terms of the GNU General Public License as published by the Free Software
Foundation, either version 3 of the License, or (at your option) any later
version.

This program is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
PARTICULAR PURPOSE. See the GNU General Public License for more details.

You should have received a copy of the GNU General Public License along with
this program. If not, see [https://www.gnu.org/licenses/](https://www.gnu.org/licenses/).

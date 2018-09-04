use parser::{
    parse_smtlib2,
    tests::repr::{
        DummySolver,
        OptionKind,
        ParseEvent,
    },
    ParseError,
};

fn assert_parse_valid_smtlib2(input: &str, expected_events: Vec<ParseEvent>) {
    let mut dummy_solver = DummySolver::default();
    parse_smtlib2(input, &mut dummy_solver).unwrap();
    let actual_events = dummy_solver.into_iter().collect::<Vec<_>>();
    assert_eq!(actual_events.len(), expected_events.len());
    for (actual, expected) in actual_events.into_iter().zip(expected_events.into_iter()) {
        assert_eq!(actual, expected)
    }
}

fn assert_parse_err(input: &str, expected_err: ParseError) {
    let mut solver = DummySolver::default();
    assert_eq!(parse_smtlib2(input, &mut solver), Err(expected_err));
}

mod paramless {
    use super::*;

    #[test]
    fn all() {
        assert_parse_valid_smtlib2("(check-sat)", vec![ParseEvent::check_sat()]);
        assert_parse_valid_smtlib2("(exit)", vec![ParseEvent::exit()]);
        assert_parse_valid_smtlib2("(get-assertions)", vec![ParseEvent::get_assertions()]);
        assert_parse_valid_smtlib2("(get-assignment)", vec![ParseEvent::get_assignment()]);
        assert_parse_valid_smtlib2("(get-model)", vec![ParseEvent::get_model()]);
        assert_parse_valid_smtlib2("(get-proof)", vec![ParseEvent::get_proof()]);
        assert_parse_valid_smtlib2(
            "(get-unsat-assumptions)",
            vec![ParseEvent::get_unsat_assumptions()],
        );
        assert_parse_valid_smtlib2("(get-unsat-core)", vec![ParseEvent::get_unsat_core()]);
        assert_parse_valid_smtlib2("(reset)", vec![ParseEvent::reset()]);
        assert_parse_valid_smtlib2("(reset-assertions)", vec![ParseEvent::reset_assertions()]);
    }

    #[test]
    fn combined() {
        assert_parse_valid_smtlib2(
            indoc!(
                "(check-sat)
                (exit)
                (get-assertions)
                (get-assignment)
                (get-model)
                (get-proof)
                (get-unsat-assumptions)
                (get-unsat-core)
                (reset)
                (reset-assertions)"
            ),
            vec![
                ParseEvent::check_sat(),
                ParseEvent::exit(),
                ParseEvent::get_assertions(),
                ParseEvent::get_assignment(),
                ParseEvent::get_model(),
                ParseEvent::get_proof(),
                ParseEvent::get_unsat_assumptions(),
                ParseEvent::get_unsat_core(),
                ParseEvent::reset(),
                ParseEvent::reset_assertions(),
            ],
        );
    }
}

#[test]
fn fixed_size() {
    assert_parse_valid_smtlib2(
        "(declare-sort FooTypeName 42)",
        vec![ParseEvent::declare_sort("FooTypeName", 42)],
    );
    assert_parse_valid_smtlib2(
        "(echo \"Hello, World!\")",
        vec![ParseEvent::echo("Hello, World!")],
    );
    assert_parse_valid_smtlib2("(push 42)", vec![ParseEvent::push(42)]);
    assert_parse_valid_smtlib2("(pop 5)", vec![ParseEvent::pop(5)]);
    assert_parse_valid_smtlib2(
        "(get-option :my-option)",
        vec![ParseEvent::get_option(OptionKind::custom(":my-option"))],
    );
    assert_parse_valid_smtlib2("(set-logic QF_ABV)", vec![ParseEvent::set_logic("QF_ABV")]);
}

mod get_info {
    use super::*;
    use lexer::TokenKind;
    use parser::tests;

    #[test]
    fn no_params() {
        assert_parse_err(
            "(get-info)",
            ParseError::unexpected_token_kind(TokenKind::CloseParen, TokenKind::Keyword),
        )
    }

    #[test]
    fn wrong_param_type() {
        assert_parse_err(
            "(get-info 42)",
            ParseError::unexpected_token_kind(TokenKind::Numeral, TokenKind::Keyword),
        );
    }

    #[test]
    fn known_flags() {
        fn assert_get_info_for(info: &str, flag: tests::GetInfoKind) {
            assert_parse_valid_smtlib2(
                &format!("(get-info {})", info),
                vec![ParseEvent::get_info(flag)],
            );
        }
        assert_get_info_for(":all-statistics", tests::GetInfoKind::AllStatistics);
        assert_get_info_for(
            ":assertion-stack-levels",
            tests::GetInfoKind::AssertionStackLevels,
        );
        assert_get_info_for(":authors", tests::GetInfoKind::Authors);
        assert_get_info_for(":error-behaviour", tests::GetInfoKind::ErrorBehaviour);
        assert_get_info_for(":name", tests::GetInfoKind::Name);
        assert_get_info_for(":reason-unknown", tests::GetInfoKind::ReasonUnknown);
        assert_get_info_for(":version", tests::GetInfoKind::Version);
    }

    #[test]
    fn custom_flag() {
        fn assert_get_info_for(info: &str) {
            assert_parse_valid_smtlib2(
                &format!("(get-info {})", info),
                vec![ParseEvent::get_info(tests::GetInfoKind::other(
                    ":my-custom-info-flag",
                ))],
            );
        }
        assert_get_info_for(":my-custom-info-flag");
    }
}

mod check_sat_assuming {
    use super::*;
    use parser::PropLit;

    #[test]
    fn empty_prop_lits() {
        assert_parse_valid_smtlib2(
            "(check-sat-assuming ())",
            vec![ParseEvent::check_sat_assuming::<_, PropLit>(vec![])],
        );
    }

    #[test]
    fn only_pos() {
        assert_parse_valid_smtlib2(
            "(check-sat-assuming (fst snd trd))",
            vec![ParseEvent::check_sat_assuming(vec![
                PropLit::pos("fst"),
                PropLit::pos("snd"),
                PropLit::pos("trd"),
            ])],
        )
    }

    #[test]
    fn only_neg() {
        assert_parse_valid_smtlib2(
            "(check-sat-assuming ((not fst) (not snd) (not trd)))",
            vec![ParseEvent::check_sat_assuming(vec![
                PropLit::neg("fst"),
                PropLit::neg("snd"),
                PropLit::neg("trd"),
            ])],
        );
    }

    #[test]
    fn mixed() {
        assert_parse_valid_smtlib2(
            "(check-sat-assuming (fst (not snd) trd))",
            vec![ParseEvent::check_sat_assuming(vec![
                PropLit::pos("fst"),
                PropLit::neg("snd"),
                PropLit::pos("trd"),
            ])],
        );
    }
}

mod set_option {
    use super::*;
    use parser::tests;
    use parser::tests::OptionAndValue::*;

    #[test]
    fn simple_bool() {
        fn assert_simple_bool(
            opt_str: &str,
            true_case: tests::OptionAndValue,
            false_case: tests::OptionAndValue,
        ) {
            assert_parse_valid_smtlib2(
                &format!("(set-option {} true)", opt_str),
                vec![ParseEvent::set_option(true_case)],
            );
            assert_parse_valid_smtlib2(
                &format!("(set-option {} false)", opt_str),
                vec![ParseEvent::set_option(false_case)],
            );
        }
        assert_simple_bool(
            ":global-declarations",
            GlobalDeclarations(true),
            GlobalDeclarations(false),
        );
        assert_simple_bool(
            ":interactive-mode",
            InteractiveMode(true),
            InteractiveMode(false),
        );
        assert_simple_bool(":print-success", PrintSuccess(true), PrintSuccess(false));
        assert_simple_bool(
            ":produce-assertions",
            ProduceAssertions(true),
            ProduceAssertions(false),
        );
        assert_simple_bool(
            ":produce-assignments",
            ProduceAssignments(true),
            ProduceAssignments(false),
        );
        assert_simple_bool(":produce-models", ProduceModels(true), ProduceModels(false));
        assert_simple_bool(":produce-proofs", ProduceProofs(true), ProduceProofs(false));
        assert_simple_bool(
            ":produce-unsat-assumptions",
            ProduceUnsatAssumptions(true),
            ProduceUnsatAssumptions(false),
        );
        assert_simple_bool(
            ":produce-unsat-cores",
            ProduceUnsatCores(true),
            ProduceUnsatCores(false),
        );
    }

    #[test]
    fn simple_numeral() {
        assert_parse_valid_smtlib2(
            "(set-option :random-seed 5)",
            vec![ParseEvent::set_option(RandomSeed(tests::NumeralLit::from(
                5_u32,
            )))],
        );
        assert_parse_valid_smtlib2(
            "(set-option :reproducible-resource-limit 42)",
            vec![ParseEvent::set_option(ReproducibleResourceLimit(
                tests::NumeralLit::from(42_u32),
            ))],
        );
        assert_parse_valid_smtlib2(
            "(set-option :verbosity 1337)",
            vec![ParseEvent::set_option(Verbosity(tests::NumeralLit::from(
                1337_u32,
            )))],
        );
    }

    #[test]
    fn simple_output_channel() {
        use parser::tests::OutputChannel;
        {
            assert_parse_valid_smtlib2(
                "(set-option :diagnostic-output-channel \"stderr\")",
                vec![ParseEvent::set_option(DiagnosticOutputChannel(
                    OutputChannel::stderr(),
                ))],
            );
            assert_parse_valid_smtlib2(
                "(set-option :diagnostic-output-channel \"stdout\")",
                vec![ParseEvent::set_option(DiagnosticOutputChannel(
                    OutputChannel::stdout(),
                ))],
            );
            assert_parse_valid_smtlib2(
                "(set-option :diagnostic-output-channel \"my_file\")",
                vec![ParseEvent::set_option(DiagnosticOutputChannel(
                    OutputChannel::file("my_file"),
                ))],
            );
        }
        {
            assert_parse_valid_smtlib2(
                "(set-option :regular-output-channel \"stderr\")",
                vec![ParseEvent::set_option(RegularOutputChannel(
                    OutputChannel::stderr(),
                ))],
            );
            assert_parse_valid_smtlib2(
                "(set-option :regular-output-channel \"stdout\")",
                vec![ParseEvent::set_option(RegularOutputChannel(
                    OutputChannel::stdout(),
                ))],
            );
            assert_parse_valid_smtlib2(
                "(set-option :regular-output-channel \"my_file\")",
                vec![ParseEvent::set_option(RegularOutputChannel(
                    OutputChannel::file("my_file"),
                ))],
            );
        }
    }

    mod simple_custom {
        use super::*;

        #[test]
        fn empty_value() {
            assert_parse_valid_smtlib2(
                "(set-option :my-custom-cmd)",
                vec![ParseEvent::set_option(tests::OptionAndValue::custom(
                    ":my-custom-cmd",
                    None,
                ))],
            );
        }

        #[test]
        fn bool_value() {
            assert_parse_valid_smtlib2(
                "(set-option :my-custom-cmd true)",
                vec![ParseEvent::set_option(tests::OptionAndValue::custom(
                    ":my-custom-cmd",
                    tests::Literal::Bool(true),
                ))],
            );
            assert_parse_valid_smtlib2(
                "(set-option :my-custom-cmd false)",
                vec![ParseEvent::set_option(tests::OptionAndValue::custom(
                    ":my-custom-cmd",
                    tests::Literal::Bool(false),
                ))],
            );
        }

        #[test]
        fn symbol_value() {
            assert_parse_valid_smtlib2(
                "(set-option :my-custom-cmd Foo)",
                vec![ParseEvent::set_option(tests::OptionAndValue::custom(
                    ":my-custom-cmd",
                    tests::Literal::symbol("Foo"),
                ))],
            );
        }

        #[test]
        fn numeral_value() {
            assert_parse_valid_smtlib2(
                "(set-option :my-custom-cmd 42)",
                vec![ParseEvent::set_option(tests::OptionAndValue::custom(
                    ":my-custom-cmd",
                    tests::Literal::numeral(42_u32),
                ))],
            );
        }

        #[test]
        fn decimal_value() {
            assert_parse_valid_smtlib2(
                "(set-option :my-custom-cmd 7.7)",
                vec![ParseEvent::set_option(tests::OptionAndValue::custom(
                    ":my-custom-cmd",
                    tests::Literal::decimal(7.7),
                ))],
            );
        }

        #[test]
        fn keyword_value() {
            assert_parse_valid_smtlib2(
                "(set-option :my-custom-cmd :my-keyword)",
                vec![ParseEvent::set_option(tests::OptionAndValue::custom(
                    ":my-custom-cmd",
                    tests::Literal::keyword(":my-keyword"),
                ))],
            );
        }
    }
}

mod set_info {
    use super::*;
    use parser::tests;
    use parser::tests::InfoAndValue::*;

    #[test]
    fn smt_lib_version() {
        assert_parse_valid_smtlib2(
            "(set-info :smt-lib-version 2.6)",
            vec![ParseEvent::set_info(SMTLibVersion(
                tests::DecimalLit::from(2.6),
            ))],
        );
    }

    #[test]
    fn source() {
        assert_parse_valid_smtlib2(
            "(set-info :source \"Hello, World!\")",
            vec![ParseEvent::set_info(Source(String::from("Hello, World!")))],
        );
        assert_parse_valid_smtlib2(
            "(set-info :source |Hello, World!|)",
            vec![ParseEvent::set_info(Source(String::from("Hello, World!")))],
        );
    }

    #[test]
    fn category() {
        use solver::ProblemCategory;
        assert_parse_valid_smtlib2(
            "(set-info :category \"crafted\")",
            vec![ParseEvent::set_info(Category(ProblemCategory::Crafted))],
        );
        assert_parse_valid_smtlib2(
            "(set-info :category \"random\")",
            vec![ParseEvent::set_info(Category(ProblemCategory::Random))],
        );
        assert_parse_valid_smtlib2(
            "(set-info :category \"industrial\")",
            vec![ParseEvent::set_info(Category(ProblemCategory::Industrial))],
        );
    }

    #[test]
    fn status() {
        use solver::ProblemStatus;
        assert_parse_valid_smtlib2(
            "(set-info :status sat)",
            vec![ParseEvent::set_info(Status(ProblemStatus::Sat))],
        );
        assert_parse_valid_smtlib2(
            "(set-info :status unsat)",
            vec![ParseEvent::set_info(Status(ProblemStatus::Unsat))],
        );
        assert_parse_valid_smtlib2(
            "(set-info :status unknown)",
            vec![ParseEvent::set_info(Status(ProblemStatus::Unknown))],
        );
    }

    #[test]
    fn license() {
        assert_parse_valid_smtlib2(
            "(set-info :license \"This is my license.\")",
            vec![ParseEvent::set_info(License(String::from(
                "This is my license.",
            )))],
        );
    }

    mod simple_custom {
        // use self::InfoAndValue::*;
        use super::*;

        #[test]
        fn empty_value() {
            assert_parse_valid_smtlib2(
                "(set-info :my-custom-info)",
                vec![ParseEvent::set_info(tests::InfoAndValue::custom(
                    ":my-custom-info",
                    None,
                ))],
            );
        }

        #[test]
        fn bool_value() {
            assert_parse_valid_smtlib2(
                "(set-info :my-custom-info true)",
                vec![ParseEvent::set_info(tests::InfoAndValue::custom(
                    ":my-custom-info",
                    tests::Literal::Bool(true),
                ))],
            );
            assert_parse_valid_smtlib2(
                "(set-info :my-custom-info false)",
                vec![ParseEvent::set_info(tests::InfoAndValue::custom(
                    ":my-custom-info",
                    tests::Literal::Bool(false),
                ))],
            );
        }

        #[test]
        fn symbol_value() {
            assert_parse_valid_smtlib2(
                "(set-info :my-custom-info Foo)",
                vec![ParseEvent::set_info(tests::InfoAndValue::custom(
                    ":my-custom-info",
                    tests::Literal::symbol("Foo"),
                ))],
            );
        }

        #[test]
        fn numeral_value() {
            assert_parse_valid_smtlib2(
                "(set-info :my-custom-info 42)",
                vec![ParseEvent::set_info(tests::InfoAndValue::custom(
                    ":my-custom-info",
                    tests::Literal::numeral(42_u32),
                ))],
            );
        }

        #[test]
        fn decimal_value() {
            assert_parse_valid_smtlib2(
                "(set-info :my-custom-info 7.7)",
                vec![ParseEvent::set_info(tests::InfoAndValue::custom(
                    ":my-custom-info",
                    tests::Literal::decimal(7.7),
                ))],
            );
        }

        #[test]
        fn keyword_value() {
            assert_parse_valid_smtlib2(
                "(set-info :my-custom-info :my-keyword)",
                vec![ParseEvent::set_info(tests::InfoAndValue::custom(
                    ":my-custom-info",
                    tests::Literal::keyword(":my-keyword"),
                ))],
            );
        }
    }
}

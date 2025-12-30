Theory vfmTestDefs2489[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stTransactionTest/SuicidesAndSendMoneyToItselfEtherDestroyed.json";
val defs = mapi (define_test "2489") tests;

Theory vfmTest1452[no_sig_docs]
Ancestors vfmTestDefs1452
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1452_0.nsv", "result1452_1.nsv", "result1452_2.nsv", "result1452_3.nsv", "result1452_4.nsv", "result1452_5.nsv", "result1452_6.nsv", "result1452_7.nsv", "result1452_8.nsv"];
val thyn = "vfmTestDefs1452";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

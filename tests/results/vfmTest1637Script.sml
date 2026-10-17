Theory vfmTest1637[no_sig_docs]
Ancestors vfmTestDefs1637
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1637_0.nsv", "result1637_1.nsv", "result1637_2.nsv", "result1637_3.nsv"];
val thyn = "vfmTestDefs1637";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

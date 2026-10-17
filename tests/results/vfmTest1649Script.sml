Theory vfmTest1649[no_sig_docs]
Ancestors vfmTestDefs1649
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1649_0.nsv", "result1649_1.nsv", "result1649_2.nsv", "result1649_3.nsv", "result1649_4.nsv", "result1649_5.nsv", "result1649_6.nsv"];
val thyn = "vfmTestDefs1649";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

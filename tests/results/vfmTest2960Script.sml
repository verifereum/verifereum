Theory vfmTest2960[no_sig_docs]
Ancestors vfmTestDefs2960
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2960_0.nsv", "result2960_1.nsv", "result2960_2.nsv", "result2960_3.nsv", "result2960_4.nsv"];
val thyn = "vfmTestDefs2960";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

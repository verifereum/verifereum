Theory vfmTest2971[no_sig_docs]
Ancestors vfmTestDefs2971
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2971_0.nsv", "result2971_1.nsv", "result2971_2.nsv", "result2971_3.nsv", "result2971_4.nsv"];
val thyn = "vfmTestDefs2971";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

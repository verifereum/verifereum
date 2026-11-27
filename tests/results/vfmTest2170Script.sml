Theory vfmTest2170[no_sig_docs]
Ancestors vfmTestDefs2170
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2170_0.nsv", "result2170_1.nsv", "result2170_2.nsv", "result2170_3.nsv", "result2170_4.nsv", "result2170_5.nsv", "result2170_6.nsv", "result2170_7.nsv"];
val thyn = "vfmTestDefs2170";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

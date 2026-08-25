Theory vfmTest2795[no_sig_docs]
Ancestors vfmTestDefs2795
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2795_0.nsv", "result2795_1.nsv", "result2795_2.nsv", "result2795_3.nsv"];
val thyn = "vfmTestDefs2795";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

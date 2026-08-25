Theory vfmTest2806[no_sig_docs]
Ancestors vfmTestDefs2806
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2806_0.nsv", "result2806_1.nsv", "result2806_2.nsv", "result2806_3.nsv"];
val thyn = "vfmTestDefs2806";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

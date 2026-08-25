Theory vfmTest2810[no_sig_docs]
Ancestors vfmTestDefs2810
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2810_0.nsv", "result2810_1.nsv", "result2810_2.nsv", "result2810_3.nsv"];
val thyn = "vfmTestDefs2810";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

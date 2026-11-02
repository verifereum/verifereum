Theory vfmTest2715[no_sig_docs]
Ancestors vfmTestDefs2715
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2715_0.nsv", "result2715_1.nsv", "result2715_2.nsv", "result2715_3.nsv", "result2715_4.nsv"];
val thyn = "vfmTestDefs2715";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

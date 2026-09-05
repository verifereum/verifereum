Theory vfmTest2325[no_sig_docs]
Ancestors vfmTestDefs2325
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2325_0.nsv", "result2325_1.nsv", "result2325_2.nsv"];
val thyn = "vfmTestDefs2325";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

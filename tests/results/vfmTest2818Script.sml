Theory vfmTest2818[no_sig_docs]
Ancestors vfmTestDefs2818
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2818_0.nsv", "result2818_1.nsv", "result2818_2.nsv", "result2818_3.nsv"];
val thyn = "vfmTestDefs2818";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

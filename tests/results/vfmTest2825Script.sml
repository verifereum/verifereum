Theory vfmTest2825[no_sig_docs]
Ancestors vfmTestDefs2825
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2825_0.nsv", "result2825_1.nsv", "result2825_2.nsv", "result2825_3.nsv"];
val thyn = "vfmTestDefs2825";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

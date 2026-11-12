Theory vfmTest2195[no_sig_docs]
Ancestors vfmTestDefs2195
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2195_0.nsv", "result2195_1.nsv", "result2195_2.nsv", "result2195_3.nsv", "result2195_4.nsv"];
val thyn = "vfmTestDefs2195";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

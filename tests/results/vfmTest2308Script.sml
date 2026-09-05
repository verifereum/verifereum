Theory vfmTest2308[no_sig_docs]
Ancestors vfmTestDefs2308
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2308_0.nsv", "result2308_1.nsv", "result2308_2.nsv", "result2308_3.nsv", "result2308_4.nsv", "result2308_5.nsv", "result2308_6.nsv"];
val thyn = "vfmTestDefs2308";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

Theory vfmTest2828[no_sig_docs]
Ancestors vfmTestDefs2828
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2828_0.nsv", "result2828_1.nsv", "result2828_2.nsv", "result2828_3.nsv"];
val thyn = "vfmTestDefs2828";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

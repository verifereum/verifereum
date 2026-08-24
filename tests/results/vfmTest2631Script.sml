Theory vfmTest2631[no_sig_docs]
Ancestors vfmTestDefs2631
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2631_0.nsv", "result2631_1.nsv", "result2631_2.nsv", "result2631_3.nsv"];
val thyn = "vfmTestDefs2631";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

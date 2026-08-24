Theory vfmTest2626[no_sig_docs]
Ancestors vfmTestDefs2626
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2626_0.nsv", "result2626_1.nsv", "result2626_2.nsv", "result2626_3.nsv"];
val thyn = "vfmTestDefs2626";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

Theory vfmTest2311[no_sig_docs]
Ancestors vfmTestDefs2311
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2311_0.nsv", "result2311_1.nsv", "result2311_2.nsv", "result2311_3.nsv", "result2311_4.nsv", "result2311_5.nsv"];
val thyn = "vfmTestDefs2311";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

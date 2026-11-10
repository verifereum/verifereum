Theory vfmTest2976[no_sig_docs]
Ancestors vfmTestDefs2976
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2976_0.nsv", "result2976_1.nsv", "result2976_2.nsv", "result2976_3.nsv", "result2976_4.nsv", "result2976_5.nsv"];
val thyn = "vfmTestDefs2976";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

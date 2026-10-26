Theory vfmTest2983[no_sig_docs]
Ancestors vfmTestDefs2983
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2983_0.nsv", "result2983_1.nsv", "result2983_2.nsv", "result2983_3.nsv", "result2983_4.nsv", "result2983_5.nsv"];
val thyn = "vfmTestDefs2983";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

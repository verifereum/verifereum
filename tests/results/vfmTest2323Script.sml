Theory vfmTest2323[no_sig_docs]
Ancestors vfmTestDefs2323
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2323_0.nsv", "result2323_1.nsv", "result2323_2.nsv", "result2323_3.nsv", "result2323_4.nsv", "result2323_5.nsv", "result2323_6.nsv", "result2323_7.nsv", "result2323_8.nsv"];
val thyn = "vfmTestDefs2323";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

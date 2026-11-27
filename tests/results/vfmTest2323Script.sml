Theory vfmTest2323[no_sig_docs]
Ancestors vfmTestDefs2323
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2323_0.nsv", "result2323_1.nsv", "result2323_2.nsv", "result2323_3.nsv", "result2323_4.nsv", "result2323_5.nsv", "result2323_6.nsv", "result2323_7.nsv", "result2323_8.nsv", "result2323_9.nsv", "result2323_10.nsv", "result2323_11.nsv", "result2323_12.nsv", "result2323_13.nsv", "result2323_14.nsv", "result2323_15.nsv", "result2323_16.nsv", "result2323_17.nsv", "result2323_18.nsv", "result2323_19.nsv"];
val thyn = "vfmTestDefs2323";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

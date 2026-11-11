Theory vfmTest2307[no_sig_docs]
Ancestors vfmTestDefs2307
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2307_0.nsv", "result2307_1.nsv", "result2307_2.nsv", "result2307_3.nsv", "result2307_4.nsv", "result2307_5.nsv", "result2307_6.nsv", "result2307_7.nsv", "result2307_8.nsv", "result2307_9.nsv", "result2307_10.nsv", "result2307_11.nsv", "result2307_12.nsv", "result2307_13.nsv", "result2307_14.nsv", "result2307_15.nsv", "result2307_16.nsv", "result2307_17.nsv", "result2307_18.nsv", "result2307_19.nsv"];
val thyn = "vfmTestDefs2307";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

Theory vfmTest2405[no_sig_docs]
Ancestors vfmTestDefs2405
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2405_0.nsv", "result2405_1.nsv", "result2405_2.nsv", "result2405_3.nsv", "result2405_4.nsv", "result2405_5.nsv", "result2405_6.nsv", "result2405_7.nsv", "result2405_8.nsv", "result2405_9.nsv", "result2405_10.nsv", "result2405_11.nsv", "result2405_12.nsv", "result2405_13.nsv", "result2405_14.nsv", "result2405_15.nsv", "result2405_16.nsv", "result2405_17.nsv", "result2405_18.nsv", "result2405_19.nsv"];
val thyn = "vfmTestDefs2405";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

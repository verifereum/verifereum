Theory vfmTest2478[no_sig_docs]
Ancestors vfmTestDefs2478
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2478_0.nsv", "result2478_1.nsv", "result2478_2.nsv", "result2478_3.nsv", "result2478_4.nsv", "result2478_5.nsv", "result2478_6.nsv", "result2478_7.nsv", "result2478_8.nsv", "result2478_9.nsv", "result2478_10.nsv", "result2478_11.nsv", "result2478_12.nsv", "result2478_13.nsv", "result2478_14.nsv", "result2478_15.nsv", "result2478_16.nsv", "result2478_17.nsv"];
val thyn = "vfmTestDefs2478";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

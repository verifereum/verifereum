Theory vfmTest1992[no_sig_docs]
Ancestors vfmTestDefs1992
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1992_0.nsv", "result1992_1.nsv", "result1992_2.nsv", "result1992_3.nsv", "result1992_4.nsv", "result1992_5.nsv", "result1992_6.nsv", "result1992_7.nsv", "result1992_8.nsv", "result1992_9.nsv", "result1992_10.nsv", "result1992_11.nsv", "result1992_12.nsv", "result1992_13.nsv", "result1992_14.nsv", "result1992_15.nsv", "result1992_16.nsv", "result1992_17.nsv", "result1992_18.nsv", "result1992_19.nsv"];
val thyn = "vfmTestDefs1992";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

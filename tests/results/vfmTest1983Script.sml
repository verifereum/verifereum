Theory vfmTest1983[no_sig_docs]
Ancestors vfmTestDefs1983
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1983_0.nsv", "result1983_1.nsv", "result1983_2.nsv", "result1983_3.nsv", "result1983_4.nsv", "result1983_5.nsv", "result1983_6.nsv", "result1983_7.nsv", "result1983_8.nsv", "result1983_9.nsv", "result1983_10.nsv", "result1983_11.nsv", "result1983_12.nsv", "result1983_13.nsv", "result1983_14.nsv", "result1983_15.nsv", "result1983_16.nsv", "result1983_17.nsv", "result1983_18.nsv", "result1983_19.nsv"];
val thyn = "vfmTestDefs1983";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

Theory vfmTest1973[no_sig_docs]
Ancestors vfmTestDefs1973
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1973_0.nsv", "result1973_1.nsv", "result1973_2.nsv", "result1973_3.nsv", "result1973_4.nsv", "result1973_5.nsv", "result1973_6.nsv", "result1973_7.nsv", "result1973_8.nsv", "result1973_9.nsv", "result1973_10.nsv", "result1973_11.nsv", "result1973_12.nsv", "result1973_13.nsv", "result1973_14.nsv", "result1973_15.nsv", "result1973_16.nsv", "result1973_17.nsv", "result1973_18.nsv", "result1973_19.nsv"];
val thyn = "vfmTestDefs1973";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

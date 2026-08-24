Theory vfmTest1980[no_sig_docs]
Ancestors vfmTestDefs1980
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1980_0.nsv", "result1980_1.nsv", "result1980_2.nsv", "result1980_3.nsv", "result1980_4.nsv", "result1980_5.nsv", "result1980_6.nsv", "result1980_7.nsv", "result1980_8.nsv", "result1980_9.nsv", "result1980_10.nsv", "result1980_11.nsv", "result1980_12.nsv", "result1980_13.nsv", "result1980_14.nsv", "result1980_15.nsv", "result1980_16.nsv", "result1980_17.nsv", "result1980_18.nsv", "result1980_19.nsv"];
val thyn = "vfmTestDefs1980";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

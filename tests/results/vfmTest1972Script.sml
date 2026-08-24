Theory vfmTest1972[no_sig_docs]
Ancestors vfmTestDefs1972
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1972_0.nsv", "result1972_1.nsv", "result1972_2.nsv", "result1972_3.nsv", "result1972_4.nsv", "result1972_5.nsv", "result1972_6.nsv", "result1972_7.nsv", "result1972_8.nsv", "result1972_9.nsv", "result1972_10.nsv", "result1972_11.nsv", "result1972_12.nsv", "result1972_13.nsv", "result1972_14.nsv", "result1972_15.nsv", "result1972_16.nsv", "result1972_17.nsv", "result1972_18.nsv", "result1972_19.nsv"];
val thyn = "vfmTestDefs1972";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

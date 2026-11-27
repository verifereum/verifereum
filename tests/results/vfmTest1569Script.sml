Theory vfmTest1569[no_sig_docs]
Ancestors vfmTestDefs1569
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1569_0.nsv", "result1569_1.nsv", "result1569_2.nsv", "result1569_3.nsv", "result1569_4.nsv", "result1569_5.nsv", "result1569_6.nsv", "result1569_7.nsv", "result1569_8.nsv", "result1569_9.nsv", "result1569_10.nsv", "result1569_11.nsv", "result1569_12.nsv", "result1569_13.nsv", "result1569_14.nsv", "result1569_15.nsv", "result1569_16.nsv", "result1569_17.nsv", "result1569_18.nsv", "result1569_19.nsv"];
val thyn = "vfmTestDefs1569";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

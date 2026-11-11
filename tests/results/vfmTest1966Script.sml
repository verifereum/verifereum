Theory vfmTest1966[no_sig_docs]
Ancestors vfmTestDefs1966
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1966_0.nsv", "result1966_1.nsv", "result1966_2.nsv", "result1966_3.nsv", "result1966_4.nsv", "result1966_5.nsv", "result1966_6.nsv", "result1966_7.nsv", "result1966_8.nsv", "result1966_9.nsv", "result1966_10.nsv", "result1966_11.nsv", "result1966_12.nsv", "result1966_13.nsv", "result1966_14.nsv", "result1966_15.nsv", "result1966_16.nsv", "result1966_17.nsv", "result1966_18.nsv", "result1966_19.nsv", "result1966_20.nsv", "result1966_21.nsv", "result1966_22.nsv", "result1966_23.nsv", "result1966_24.nsv", "result1966_25.nsv", "result1966_26.nsv", "result1966_27.nsv", "result1966_28.nsv", "result1966_29.nsv"];
val thyn = "vfmTestDefs1966";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

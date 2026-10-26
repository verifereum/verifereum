Theory vfmTest1083[no_sig_docs]
Ancestors vfmTestDefs1083
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1083_0.nsv", "result1083_1.nsv", "result1083_2.nsv", "result1083_3.nsv", "result1083_4.nsv", "result1083_5.nsv", "result1083_6.nsv", "result1083_7.nsv", "result1083_8.nsv", "result1083_9.nsv", "result1083_10.nsv", "result1083_11.nsv", "result1083_12.nsv", "result1083_13.nsv", "result1083_14.nsv", "result1083_15.nsv", "result1083_16.nsv", "result1083_17.nsv", "result1083_18.nsv", "result1083_19.nsv", "result1083_20.nsv", "result1083_21.nsv", "result1083_22.nsv", "result1083_23.nsv", "result1083_24.nsv"];
val thyn = "vfmTestDefs1083";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

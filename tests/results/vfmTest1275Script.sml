Theory vfmTest1275[no_sig_docs]
Ancestors vfmTestDefs1275
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1275_0.nsv", "result1275_1.nsv", "result1275_2.nsv", "result1275_3.nsv", "result1275_4.nsv", "result1275_5.nsv", "result1275_6.nsv", "result1275_7.nsv", "result1275_8.nsv", "result1275_9.nsv", "result1275_10.nsv", "result1275_11.nsv", "result1275_12.nsv", "result1275_13.nsv", "result1275_14.nsv", "result1275_15.nsv", "result1275_16.nsv", "result1275_17.nsv", "result1275_18.nsv", "result1275_19.nsv", "result1275_20.nsv", "result1275_21.nsv", "result1275_22.nsv", "result1275_23.nsv", "result1275_24.nsv", "result1275_25.nsv", "result1275_26.nsv"];
val thyn = "vfmTestDefs1275";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

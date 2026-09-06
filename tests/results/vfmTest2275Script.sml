Theory vfmTest2275[no_sig_docs]
Ancestors vfmTestDefs2275
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2275_0.nsv", "result2275_1.nsv", "result2275_2.nsv", "result2275_3.nsv", "result2275_4.nsv", "result2275_5.nsv", "result2275_6.nsv", "result2275_7.nsv", "result2275_8.nsv", "result2275_9.nsv", "result2275_10.nsv", "result2275_11.nsv", "result2275_12.nsv", "result2275_13.nsv", "result2275_14.nsv", "result2275_15.nsv", "result2275_16.nsv", "result2275_17.nsv", "result2275_18.nsv", "result2275_19.nsv", "result2275_20.nsv", "result2275_21.nsv", "result2275_22.nsv", "result2275_23.nsv", "result2275_24.nsv", "result2275_25.nsv", "result2275_26.nsv", "result2275_27.nsv", "result2275_28.nsv", "result2275_29.nsv", "result2275_30.nsv"];
val thyn = "vfmTestDefs2275";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

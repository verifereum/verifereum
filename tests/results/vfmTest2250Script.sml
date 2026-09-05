Theory vfmTest2250[no_sig_docs]
Ancestors vfmTestDefs2250
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2250_0.nsv", "result2250_1.nsv", "result2250_2.nsv", "result2250_3.nsv", "result2250_4.nsv", "result2250_5.nsv", "result2250_6.nsv", "result2250_7.nsv", "result2250_8.nsv", "result2250_9.nsv", "result2250_10.nsv", "result2250_11.nsv", "result2250_12.nsv", "result2250_13.nsv", "result2250_14.nsv", "result2250_15.nsv", "result2250_16.nsv", "result2250_17.nsv", "result2250_18.nsv", "result2250_19.nsv", "result2250_20.nsv", "result2250_21.nsv", "result2250_22.nsv", "result2250_23.nsv", "result2250_24.nsv", "result2250_25.nsv"];
val thyn = "vfmTestDefs2250";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

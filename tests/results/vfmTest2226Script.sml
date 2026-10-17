Theory vfmTest2226[no_sig_docs]
Ancestors vfmTestDefs2226
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2226_0.nsv", "result2226_1.nsv", "result2226_2.nsv", "result2226_3.nsv", "result2226_4.nsv", "result2226_5.nsv", "result2226_6.nsv", "result2226_7.nsv", "result2226_8.nsv", "result2226_9.nsv", "result2226_10.nsv", "result2226_11.nsv", "result2226_12.nsv", "result2226_13.nsv", "result2226_14.nsv", "result2226_15.nsv", "result2226_16.nsv", "result2226_17.nsv", "result2226_18.nsv", "result2226_19.nsv", "result2226_20.nsv", "result2226_21.nsv", "result2226_22.nsv", "result2226_23.nsv", "result2226_24.nsv", "result2226_25.nsv"];
val thyn = "vfmTestDefs2226";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

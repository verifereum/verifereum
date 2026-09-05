Theory vfmTest2356[no_sig_docs]
Ancestors vfmTestDefs2356
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2356_0.nsv", "result2356_1.nsv", "result2356_2.nsv", "result2356_3.nsv", "result2356_4.nsv", "result2356_5.nsv", "result2356_6.nsv", "result2356_7.nsv", "result2356_8.nsv", "result2356_9.nsv", "result2356_10.nsv", "result2356_11.nsv", "result2356_12.nsv", "result2356_13.nsv", "result2356_14.nsv", "result2356_15.nsv", "result2356_16.nsv", "result2356_17.nsv", "result2356_18.nsv", "result2356_19.nsv", "result2356_20.nsv", "result2356_21.nsv", "result2356_22.nsv", "result2356_23.nsv", "result2356_24.nsv", "result2356_25.nsv", "result2356_26.nsv", "result2356_27.nsv", "result2356_28.nsv", "result2356_29.nsv", "result2356_30.nsv", "result2356_31.nsv", "result2356_32.nsv"];
val thyn = "vfmTestDefs2356";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

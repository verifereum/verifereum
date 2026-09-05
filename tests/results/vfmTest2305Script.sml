Theory vfmTest2305[no_sig_docs]
Ancestors vfmTestDefs2305
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2305_0.nsv", "result2305_1.nsv", "result2305_2.nsv", "result2305_3.nsv", "result2305_4.nsv", "result2305_5.nsv", "result2305_6.nsv", "result2305_7.nsv", "result2305_8.nsv", "result2305_9.nsv", "result2305_10.nsv", "result2305_11.nsv", "result2305_12.nsv", "result2305_13.nsv", "result2305_14.nsv", "result2305_15.nsv", "result2305_16.nsv", "result2305_17.nsv", "result2305_18.nsv", "result2305_19.nsv", "result2305_20.nsv", "result2305_21.nsv", "result2305_22.nsv", "result2305_23.nsv", "result2305_24.nsv", "result2305_25.nsv", "result2305_26.nsv"];
val thyn = "vfmTestDefs2305";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

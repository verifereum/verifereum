Theory vfmTest2986[no_sig_docs]
Ancestors vfmTestDefs2986
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2986_0.nsv", "result2986_1.nsv", "result2986_2.nsv", "result2986_3.nsv", "result2986_4.nsv", "result2986_5.nsv", "result2986_6.nsv", "result2986_7.nsv", "result2986_8.nsv", "result2986_9.nsv", "result2986_10.nsv", "result2986_11.nsv", "result2986_12.nsv", "result2986_13.nsv", "result2986_14.nsv", "result2986_15.nsv", "result2986_16.nsv", "result2986_17.nsv", "result2986_18.nsv", "result2986_19.nsv", "result2986_20.nsv", "result2986_21.nsv", "result2986_22.nsv", "result2986_23.nsv", "result2986_24.nsv", "result2986_25.nsv", "result2986_26.nsv"];
val thyn = "vfmTestDefs2986";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

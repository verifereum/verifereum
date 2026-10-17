Theory vfmTest2192[no_sig_docs]
Ancestors vfmTestDefs2192
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2192_0.nsv", "result2192_1.nsv", "result2192_2.nsv", "result2192_3.nsv", "result2192_4.nsv", "result2192_5.nsv", "result2192_6.nsv", "result2192_7.nsv", "result2192_8.nsv", "result2192_9.nsv", "result2192_10.nsv", "result2192_11.nsv", "result2192_12.nsv", "result2192_13.nsv", "result2192_14.nsv", "result2192_15.nsv", "result2192_16.nsv", "result2192_17.nsv", "result2192_18.nsv", "result2192_19.nsv", "result2192_20.nsv", "result2192_21.nsv", "result2192_22.nsv", "result2192_23.nsv"];
val thyn = "vfmTestDefs2192";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

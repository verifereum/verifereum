Theory vfmTest2072[no_sig_docs]
Ancestors vfmTestDefs2072
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2072_0.nsv", "result2072_1.nsv", "result2072_2.nsv", "result2072_3.nsv", "result2072_4.nsv", "result2072_5.nsv", "result2072_6.nsv", "result2072_7.nsv", "result2072_8.nsv", "result2072_9.nsv", "result2072_10.nsv", "result2072_11.nsv", "result2072_12.nsv", "result2072_13.nsv", "result2072_14.nsv", "result2072_15.nsv", "result2072_16.nsv", "result2072_17.nsv", "result2072_18.nsv", "result2072_19.nsv", "result2072_20.nsv", "result2072_21.nsv", "result2072_22.nsv", "result2072_23.nsv"];
val thyn = "vfmTestDefs2072";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

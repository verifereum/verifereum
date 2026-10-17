Theory vfmTest2424[no_sig_docs]
Ancestors vfmTestDefs2424
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2424_0.nsv", "result2424_1.nsv", "result2424_2.nsv", "result2424_3.nsv", "result2424_4.nsv", "result2424_5.nsv", "result2424_6.nsv", "result2424_7.nsv", "result2424_8.nsv", "result2424_9.nsv", "result2424_10.nsv", "result2424_11.nsv", "result2424_12.nsv", "result2424_13.nsv", "result2424_14.nsv", "result2424_15.nsv", "result2424_16.nsv", "result2424_17.nsv", "result2424_18.nsv", "result2424_19.nsv"];
val thyn = "vfmTestDefs2424";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

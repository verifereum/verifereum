Theory vfmTest2210[no_sig_docs]
Ancestors vfmTestDefs2210
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2210_0.nsv", "result2210_1.nsv", "result2210_2.nsv", "result2210_3.nsv", "result2210_4.nsv", "result2210_5.nsv", "result2210_6.nsv", "result2210_7.nsv", "result2210_8.nsv", "result2210_9.nsv", "result2210_10.nsv", "result2210_11.nsv", "result2210_12.nsv", "result2210_13.nsv", "result2210_14.nsv", "result2210_15.nsv", "result2210_16.nsv", "result2210_17.nsv", "result2210_18.nsv"];
val thyn = "vfmTestDefs2210";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

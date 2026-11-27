Theory vfmTest2089[no_sig_docs]
Ancestors vfmTestDefs2089
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2089_0.nsv", "result2089_1.nsv", "result2089_2.nsv", "result2089_3.nsv", "result2089_4.nsv", "result2089_5.nsv", "result2089_6.nsv", "result2089_7.nsv", "result2089_8.nsv", "result2089_9.nsv", "result2089_10.nsv", "result2089_11.nsv", "result2089_12.nsv", "result2089_13.nsv", "result2089_14.nsv", "result2089_15.nsv"];
val thyn = "vfmTestDefs2089";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

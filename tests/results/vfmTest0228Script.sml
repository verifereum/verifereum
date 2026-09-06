Theory vfmTest0228[no_sig_docs]
Ancestors vfmTestDefs0228
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0228_0.nsv", "result0228_1.nsv", "result0228_2.nsv", "result0228_3.nsv", "result0228_4.nsv", "result0228_5.nsv", "result0228_6.nsv", "result0228_7.nsv", "result0228_8.nsv", "result0228_9.nsv", "result0228_10.nsv", "result0228_11.nsv", "result0228_12.nsv", "result0228_13.nsv", "result0228_14.nsv", "result0228_15.nsv"];
val thyn = "vfmTestDefs0228";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

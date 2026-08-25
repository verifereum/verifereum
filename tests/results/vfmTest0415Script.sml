Theory vfmTest0415[no_sig_docs]
Ancestors vfmTestDefs0415
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0415_0.nsv", "result0415_1.nsv", "result0415_2.nsv", "result0415_3.nsv", "result0415_4.nsv", "result0415_5.nsv", "result0415_6.nsv", "result0415_7.nsv", "result0415_8.nsv", "result0415_9.nsv", "result0415_10.nsv", "result0415_11.nsv", "result0415_12.nsv", "result0415_13.nsv", "result0415_14.nsv", "result0415_15.nsv", "result0415_16.nsv", "result0415_17.nsv", "result0415_18.nsv", "result0415_19.nsv", "result0415_20.nsv", "result0415_21.nsv"];
val thyn = "vfmTestDefs0415";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

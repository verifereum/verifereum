Theory vfmTest0778[no_sig_docs]
Ancestors vfmTestDefs0778
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0778_0.nsv", "result0778_1.nsv", "result0778_2.nsv", "result0778_3.nsv", "result0778_4.nsv", "result0778_5.nsv", "result0778_6.nsv", "result0778_7.nsv", "result0778_8.nsv", "result0778_9.nsv", "result0778_10.nsv", "result0778_11.nsv", "result0778_12.nsv", "result0778_13.nsv", "result0778_14.nsv", "result0778_15.nsv", "result0778_16.nsv", "result0778_17.nsv", "result0778_18.nsv", "result0778_19.nsv", "result0778_20.nsv", "result0778_21.nsv", "result0778_22.nsv", "result0778_23.nsv", "result0778_24.nsv", "result0778_25.nsv", "result0778_26.nsv", "result0778_27.nsv", "result0778_28.nsv", "result0778_29.nsv", "result0778_30.nsv", "result0778_31.nsv"];
val thyn = "vfmTestDefs0778";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

Theory vfmTest0210[no_sig_docs]
Ancestors vfmTestDefs0210
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0210_0.nsv", "result0210_1.nsv", "result0210_2.nsv", "result0210_3.nsv", "result0210_4.nsv", "result0210_5.nsv", "result0210_6.nsv", "result0210_7.nsv", "result0210_8.nsv", "result0210_9.nsv", "result0210_10.nsv", "result0210_11.nsv", "result0210_12.nsv", "result0210_13.nsv", "result0210_14.nsv", "result0210_15.nsv", "result0210_16.nsv", "result0210_17.nsv", "result0210_18.nsv", "result0210_19.nsv", "result0210_20.nsv", "result0210_21.nsv", "result0210_22.nsv", "result0210_23.nsv", "result0210_24.nsv", "result0210_25.nsv", "result0210_26.nsv", "result0210_27.nsv", "result0210_28.nsv", "result0210_29.nsv"];
val thyn = "vfmTestDefs0210";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

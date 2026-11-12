Theory vfmTest0021[no_sig_docs]
Ancestors vfmTestDefs0021
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0021_0.nsv", "result0021_1.nsv", "result0021_2.nsv", "result0021_3.nsv", "result0021_4.nsv", "result0021_5.nsv", "result0021_6.nsv", "result0021_7.nsv", "result0021_8.nsv", "result0021_9.nsv", "result0021_10.nsv", "result0021_11.nsv", "result0021_12.nsv", "result0021_13.nsv", "result0021_14.nsv", "result0021_15.nsv", "result0021_16.nsv", "result0021_17.nsv", "result0021_18.nsv", "result0021_19.nsv", "result0021_20.nsv", "result0021_21.nsv", "result0021_22.nsv", "result0021_23.nsv", "result0021_24.nsv", "result0021_25.nsv", "result0021_26.nsv", "result0021_27.nsv", "result0021_28.nsv"];
val thyn = "vfmTestDefs0021";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

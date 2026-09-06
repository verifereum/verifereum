Theory vfmTest0026[no_sig_docs]
Ancestors vfmTestDefs0026
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0026_0.nsv", "result0026_1.nsv", "result0026_2.nsv", "result0026_3.nsv", "result0026_4.nsv", "result0026_5.nsv", "result0026_6.nsv", "result0026_7.nsv", "result0026_8.nsv", "result0026_9.nsv", "result0026_10.nsv", "result0026_11.nsv", "result0026_12.nsv", "result0026_13.nsv", "result0026_14.nsv", "result0026_15.nsv", "result0026_16.nsv", "result0026_17.nsv", "result0026_18.nsv", "result0026_19.nsv", "result0026_20.nsv", "result0026_21.nsv", "result0026_22.nsv", "result0026_23.nsv", "result0026_24.nsv", "result0026_25.nsv", "result0026_26.nsv", "result0026_27.nsv", "result0026_28.nsv", "result0026_29.nsv", "result0026_30.nsv", "result0026_31.nsv", "result0026_32.nsv"];
val thyn = "vfmTestDefs0026";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

Theory vfmTest0055[no_sig_docs]
Ancestors vfmTestDefs0055
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0055_0.nsv", "result0055_1.nsv", "result0055_2.nsv", "result0055_3.nsv", "result0055_4.nsv", "result0055_5.nsv", "result0055_6.nsv", "result0055_7.nsv", "result0055_8.nsv", "result0055_9.nsv", "result0055_10.nsv", "result0055_11.nsv", "result0055_12.nsv", "result0055_13.nsv", "result0055_14.nsv", "result0055_15.nsv", "result0055_16.nsv", "result0055_17.nsv", "result0055_18.nsv", "result0055_19.nsv", "result0055_20.nsv", "result0055_21.nsv", "result0055_22.nsv", "result0055_23.nsv", "result0055_24.nsv", "result0055_25.nsv", "result0055_26.nsv", "result0055_27.nsv", "result0055_28.nsv", "result0055_29.nsv"];
val thyn = "vfmTestDefs0055";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

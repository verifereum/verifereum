Theory vfmTest1055[no_sig_docs]
Ancestors vfmTestDefs1055
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1055_0.nsv", "result1055_1.nsv", "result1055_2.nsv", "result1055_3.nsv", "result1055_4.nsv", "result1055_5.nsv", "result1055_6.nsv", "result1055_7.nsv", "result1055_8.nsv", "result1055_9.nsv", "result1055_10.nsv", "result1055_11.nsv", "result1055_12.nsv", "result1055_13.nsv", "result1055_14.nsv", "result1055_15.nsv", "result1055_16.nsv", "result1055_17.nsv", "result1055_18.nsv", "result1055_19.nsv", "result1055_20.nsv", "result1055_21.nsv", "result1055_22.nsv", "result1055_23.nsv", "result1055_24.nsv", "result1055_25.nsv", "result1055_26.nsv", "result1055_27.nsv", "result1055_28.nsv", "result1055_29.nsv", "result1055_30.nsv", "result1055_31.nsv", "result1055_32.nsv", "result1055_33.nsv", "result1055_34.nsv", "result1055_35.nsv"];
val thyn = "vfmTestDefs1055";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

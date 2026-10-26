Theory vfmTest3055[no_sig_docs]
Ancestors vfmTestDefs3055
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3055_0.nsv", "result3055_1.nsv", "result3055_2.nsv", "result3055_3.nsv", "result3055_4.nsv", "result3055_5.nsv", "result3055_6.nsv", "result3055_7.nsv", "result3055_8.nsv"];
val thyn = "vfmTestDefs3055";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

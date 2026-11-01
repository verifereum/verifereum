Theory vfmTest0055[no_sig_docs]
Ancestors vfmTestDefs0055
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0055_0.nsv", "result0055_1.nsv", "result0055_2.nsv", "result0055_3.nsv", "result0055_4.nsv", "result0055_5.nsv", "result0055_6.nsv", "result0055_7.nsv", "result0055_8.nsv", "result0055_9.nsv"];
val thyn = "vfmTestDefs0055";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

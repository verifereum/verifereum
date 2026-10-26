Theory vfmTest3006[no_sig_docs]
Ancestors vfmTestDefs3006
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3006_0.nsv", "result3006_1.nsv", "result3006_2.nsv", "result3006_3.nsv", "result3006_4.nsv", "result3006_5.nsv", "result3006_6.nsv", "result3006_7.nsv"];
val thyn = "vfmTestDefs3006";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

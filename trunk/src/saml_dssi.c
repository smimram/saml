/*************************************
 * Begining of the DSSI general part *
 *************************************/

#include <ladspa.h>
#include <dssi.h>
#include <stdio.h>
#include <assert.h>

static LADSPA_Descriptor *SAML_LADSPA_descriptor = NULL;
static DSSI_Descriptor *SAML_DSSI_descriptor = NULL;

const LADSPA_Descriptor *ladspa_descriptor(unsigned long index)
{
    switch (index)
      {
      case 0:
        return SAML_LADSPA_descriptor;
      default:
        return NULL;
      }
}

const DSSI_Descriptor *dssi_descriptor(unsigned long index)
{
  switch (index)
    {
    case 0:
      return SAML_DSSI_descriptor;
    default:
      return NULL;
    }
}

#define POLYPHONY 32
#define SAML_PORT_OUTPUT_L 0
#define SAML_PORT_OUTPUT_R 1

typedef struct
{
  LADSPA_Data *output_l;
  LADSPA_Data *output_r;
  /* Internal state of a voice. */
  STATE *state[POLYPHONY];
  /* Note played by a voice. */
  unsigned long note[POLYPHONY];
  /* First inactive voice. */
  int first_inactive;
} SAML_synth_t;

/* Allocate the internal structures of the synth. */
static LADSPA_Handle SAML_instantiate(const LADSPA_Descriptor *descriptor, unsigned long sample_rate)
{
  SAML_synth_t *h = malloc(sizeof(SAML_synth_t));
  int i;

  for (i = 0; i < POLYPHONY; i++)
    {
      h->state[i] = SAML_synth_alloc();
      h->state[i]->period = 1. / (float)sample_rate;
    }
  h->first_inactive=0;

  return (LADSPA_Handle)h;
}

static void SAML_connect_port(LADSPA_Handle instance, unsigned long port, LADSPA_Data *data)
{
  SAML_synth_t *h = (SAML_synth_t*)instance;
  switch(port)
    {
    case SAML_PORT_OUTPUT_L:
      h->output_l = data;
      break;

    case SAML_PORT_OUTPUT_R:
      h->output_r = data;
      break;
    }
}

/* Reset the synth. */
static void SAML_activate(LADSPA_Handle instance)
{
  SAML_synth_t *h = (SAML_synth_t*)instance;
  int i;

  for (i = 0; i < h->first_inactive; i++)
    SAML_synth_reset(h->state[i]);
}

/* Mute all voices. */
void SAML_deactivate(LADSPA_Handle instance)
{
  SAML_synth_t *h = (SAML_synth_t*)instance;
  int i;

  for (i = 0; i < h->first_inactive; i++)
    SAML_synth_reset(h->state[i]);
}

/* Free internal structures of the synth. */
static void SAML_cleanup(LADSPA_Handle instance)
{
  SAML_synth_t *h = (SAML_synth_t*)instance;
  int i;

  for (i = 0; i < POLYPHONY; i++)
    SAML_synth_free(h->state[i]);
  free(h);
}

char *SAML_configure(LADSPA_Handle instance, const char *key, const char *value)
{
  /* TODO: we might want to handle some configure operations */
  return NULL;
}

const DSSI_Program_Descriptor *SAML_get_program(LADSPA_Handle instance, unsigned long index)
{
  /* TODO: return program descriptor */
  return NULL;
}

void SAML_select_program(LADSPA_Handle handle, unsigned long bank, unsigned long program)
{
  /* TODO */
}

int SAML_get_midi_controller(LADSPA_Handle instance, unsigned long port)
{
  /* TODO: return the MIDI controller associated with a given port */
  return DSSI_NONE;
}

static void SAML_run_synth(LADSPA_Handle instance, unsigned long sample_count, snd_seq_event_t *events, unsigned long event_count)
{
  SAML_synth_t *h = (SAML_synth_t*)instance;
  unsigned long pos, event_pos, note, n;

  if (event_count > 0) {
    //printf("synth: we have %ld events\n", event_count);
  }

  /* Pack notes */
  for (n = 0; n < h->first_inactive; n++)
    if (!SAML_synth_is_active(h->state[n]))
      {
        STATE *tmp;
        unsigned long l = h->first_inactive-1;
        tmp = h->state[n];
        h->state[n] = h->state[l];
        h->state[l] = tmp;
        h->note[n] = h->note[l];
        h->first_inactive--;
      }

  for (pos = 0, event_pos = 0; pos < sample_count; pos++)
    {
      while (event_pos < event_count && pos == events[event_pos].time.tick)
        {
          //printf("synth: event type %d\n", events[event_pos].type);

          if (events[event_pos].type == SND_SEQ_EVENT_NOTEON && h->first_inactive < POLYPHONY)
            {
              note = events[event_pos].data.note.note;
              n = h->first_inactive;
              h->first_inactive++;
              SAML_synth_reset(h->state[n]);
              SAML_synth_set_velocity(h->state[n], (float)events[event_pos].data.note.velocity / 127.0f);
              printf("note on : %ld (vel: %d)\n", note, events[event_pos].data.note.velocity);
              h->note[n] = note;
              SAML_synth_set_freq(h->state[n], 440. * pow(2.,(note - 69.)/12.));
              SAML_synth_activate(h->state[n]);
            }
          else if (events[event_pos].type == SND_SEQ_EVENT_NOTEOFF)
            {
              note = events[event_pos].data.note.note;
              printf("note off: %ld\n", note);
              for (n = 0; n < h->first_inactive; n++)
                if (h->note[n] == note)
                  SAML_synth_note_off(h->state[n]);
            }
          event_pos++;
        }

      h->output_l[pos] = 0.0f;
      h->output_r[pos] = 0.0f;
      for (n = 0; n < h->first_inactive; n++)
        if (SAML_synth_is_active(h->state[n]))
          {
            /* LADSPA_Data s = SAML_synth(h->state[n]); */
            pair_double_double s = SAML_synth(h->state[n]);
            h->output_l[pos] += s.x;
            h->output_r[pos] += s.y;
          }
    }
}

static void SAML_ladspa_run(LADSPA_Handle instance, unsigned long sample_count)
{
  SAML_run_synth(instance, sample_count, NULL, 0);
}

__attribute__((constructor)) void init()
{
  char **port_names;
  LADSPA_PortDescriptor *port_descriptors;
  LADSPA_PortRangeHint *port_range_hints;

  SAML_LADSPA_descriptor = malloc(sizeof(LADSPA_Descriptor));

  if (SAML_LADSPA_descriptor)
    {
      SAML_LADSPA_descriptor->UniqueID = 12345;
      SAML_LADSPA_descriptor->Label = "saml_synth";
      SAML_LADSPA_descriptor->Properties = 0;
      SAML_LADSPA_descriptor->Name = SAML_name;
      SAML_LADSPA_descriptor->Maker = "SAML/Liquidsoap";
      SAML_LADSPA_descriptor->Copyright = "(c)";
      SAML_LADSPA_descriptor->PortCount = 2;

      port_descriptors = calloc(SAML_LADSPA_descriptor->PortCount, sizeof(LADSPA_PortDescriptor));
      SAML_LADSPA_descriptor->PortDescriptors = port_descriptors;
      port_range_hints = calloc(SAML_LADSPA_descriptor->PortCount, sizeof(LADSPA_PortRangeHint));
      SAML_LADSPA_descriptor->PortRangeHints = port_range_hints;
      port_names = calloc(SAML_LADSPA_descriptor->PortCount, sizeof(char*));
      SAML_LADSPA_descriptor->PortNames = (const char**)port_names;

      /* Declare the ports. */
      port_descriptors[SAML_PORT_OUTPUT_L] = LADSPA_PORT_OUTPUT | LADSPA_PORT_AUDIO;
      port_names[SAML_PORT_OUTPUT_L] = "Left output";
      port_range_hints[SAML_PORT_OUTPUT_L].HintDescriptor = 0;
      port_descriptors[SAML_PORT_OUTPUT_R] = LADSPA_PORT_OUTPUT | LADSPA_PORT_AUDIO;
      port_names[SAML_PORT_OUTPUT_R] = "Right output";
      port_range_hints[SAML_PORT_OUTPUT_R].HintDescriptor = 0;

      SAML_LADSPA_descriptor->instantiate = SAML_instantiate;
      SAML_LADSPA_descriptor->connect_port = SAML_connect_port;
      SAML_LADSPA_descriptor->activate = SAML_activate;
      SAML_LADSPA_descriptor->run = SAML_ladspa_run;
      SAML_LADSPA_descriptor->run_adding = NULL;
      SAML_LADSPA_descriptor->set_run_adding_gain = NULL;
      SAML_LADSPA_descriptor->deactivate = SAML_deactivate;
      SAML_LADSPA_descriptor->cleanup = SAML_cleanup;
    }

  SAML_DSSI_descriptor = malloc(sizeof(DSSI_Descriptor));

  if (SAML_DSSI_descriptor)
    {
      SAML_DSSI_descriptor->DSSI_API_Version = 1;
      SAML_DSSI_descriptor->LADSPA_Plugin = SAML_LADSPA_descriptor;
      SAML_DSSI_descriptor->configure = NULL; /* SAML_configure; */
      SAML_DSSI_descriptor->get_program = NULL; /* SAML_get_program; */
      SAML_DSSI_descriptor->select_program = NULL; /* SAML_select_program; */
      SAML_DSSI_descriptor->get_midi_controller_for_port = SAML_get_midi_controller;
      SAML_DSSI_descriptor->run_synth = SAML_run_synth;
      SAML_DSSI_descriptor->run_synth_adding = NULL;
      SAML_DSSI_descriptor->run_multiple_synths = NULL;
      SAML_DSSI_descriptor->run_multiple_synths_adding = NULL;
    }
}

__attribute__((constructor)) void fini()
{
  if (SAML_LADSPA_descriptor)
    {
      free((LADSPA_PortDescriptor*)SAML_LADSPA_descriptor->PortDescriptors);
      free((char**)SAML_LADSPA_descriptor->PortNames);
      free((LADSPA_PortRangeHint*)SAML_LADSPA_descriptor->PortRangeHints);
      free(SAML_LADSPA_descriptor);
    }
  if (SAML_DSSI_descriptor)
    {
      free(SAML_DSSI_descriptor);
    }
}
